## Tagged DFA, for matching and submatch extraction.
##
## A TDFA state is the list of NFA states that are
## alive after consuming some text, kept in priority
## order. Priority order plus discarding lower priority
## duplicates gives leftmost-first (PCRE) semantics.
##
## Captures are last capture wins, same as PCRE.
## Every group has two tags, its start and its end.
## Every NFA state in a TDFA state owns a set of
## registers, one per tag, holding text positions;
## the NFA state position in the list is the set index.
## Transitions carry one operation per target NFA state:
## copy the registers of a source NFA state, and set
## some tags to the current text position.
##
## Chars in the alphabet (ASCII and expression chars)
## are resolved at compile time. Any other rune
## evaluates the state's predicates (``\s``, ``\pL``,
## ``[^a]``, etc) at runtime and picks one of the
## precomputed transitions for every combination
## of their results.
##
## Assertions depend on the previous and next chars.
## The next char is known by the transition. The
## previous char is part of the state: its context
## is the result of the previous char tests the regex
## assertions use (start of text, new line, word char).
##
## In find mode, the last NFA state of every TDFA
## state is a restart thread (``restartNfa``), with the
## lowest priority, that starts a new match at the
## current position. A transition accepts before
## consuming its char if an NFA state reaches the end
## of the expression; lower priority NFA states and the
## restart thread are discarded then, same as PCRE.

import std/unicode
import std/tables
import std/hashes
import std/algorithm
import std/sets

import nodetype
import nodematch
import nfa
import common

type
  TdfaMode* = enum
    tmMatch  ## anchored at start and end
    tmFind   ## leftmost-first search
  TdfaOp* = tuple
    ## target registers = source registers + tags.
    ## A source of ``fresh`` means all registers unset
    src: int16
    tags: int16  # index into ``Tdfa.tags``, -1 if none
  TdfaTrans* = object
    target*: int32  ## -1 if no NFA state survives
    ops*: seq[TdfaOp]
    accept*: TdfaOp
      ## registers of the match, set before consuming
      ## the char; ``accept.src == noAccept`` if none
  TdfaState* = object
    nfaStates*: seq[int16]
    ctx*: int16  ## previous char context
    syms*: seq[tuple[sym, trans: int32]]
    preds*: seq[seq[Node]]
      ## predicates for runes not in the alphabet,
      ## every predicate is a conjunction of nodes
    predTrans*: seq[int32]
      ## transition for every combination of
      ## predicate results; -1 for no match
    eoe*: int32
      ## end of text transition; its ``accept``
      ## is the match, if any; -1 if no match
  CtxTest* = enum
    ## previous char tests used by assertions
    ctStart, ctStartNl, ctWord, ctWordAscii
  Tdfa* = object
    mode*: TdfaMode
    states*: seq[TdfaState]
    trans*: seq[TdfaTrans]
    tags*: seq[seq[int16]]
      ## tags set by a transition; a tag is ``group*2``
      ## for start, ``group*2+1`` for end; tag ``nTags-1``
      ## is the match start in find mode
    nTags*: int  ## registers per NFA state
    maxRegs*: int  ## max NFA states per TDFA state
    alphabet*: seq[int32]  ## chars resolved at compile time
    ctxTests*: set[CtxTest]
    initStates*: seq[int32]  ## initial state by context
    # runtime matcher tables, see ``tdfamatch``
    asciiTrans*: seq[int32]
      ## transition of state ``q`` on ASCII char
      ## ``c`` at ``q*128+c``; -1 if none
    nonAsciiSyms*: seq[seq[tuple[sym, trans: int32]]]
      ## non-ASCII alphabet transitions by state, sorted
    nonAsciiAlphabet*: seq[int32]  ## sorted

const
  restartNfa* = -1'i16  ## restart NFA state, see find mode
  fresh* = -1'i16  ## source of a new thread
  noAccept* = -2'i16
  maxStates = 10000
  maxPreds = 8

func hash(t: TdfaTrans): Hash =
  hash((t.target, t.ops, t.accept))

type
  Matcher = enum
    mFalse, mTrue, mPred

func eq(a, b: Node): bool =
  ## compare the matching related fields
  if a.kind != b.kind or a.cp != b.cp or
      a.cc.int32 != b.cc.int32 or
      a.cps != b.cps or a.ranges != b.ranges or
      a.shorthands.len != b.shorthands.len:
    return false
  for i in 0 .. a.shorthands.len-1:
    if not eq(a.shorthands[i], b.shorthands[i]):
      return false
  return true

func eq(a, b: seq[Node]): bool =
  if a.len != b.len:
    return false
  for i in 0 .. a.len-1:
    if not eq(a[i], b[i]):
      return false
  return true

func find(preds: seq[seq[Node]], p: seq[Node]): int =
  for i, p2 in preds.pairs:
    if eq(p, p2):
      return i
  return -1

func bare(n: Node): Node =
  ## node without transitions, for comparison
  result = n
  result.next.setLen 0

func zOf(transitions: Transitions, n, nti: int): seq[Node] =
  if transitions.allZ.len == 0:
    return
  let zi = transitions.allZ[n][nti]
  if zi != -1:
    result = transitions.z[zi]

func filters(transitions: Transitions, n, nti: int): seq[Node] =
  ## match-transition nodes the char has to match
  for z in zOf(transitions, n, nti):
    if z.kind in matchTransitionKind:
      result.add z.bare

func tagsOf(transitions: Transitions, n, nti: int): seq[int16] =
  for z in zOf(transitions, n, nti):
    if z.kind in groupKind:
      let tag = z.idx*2 + int16(z.kind == reGroupEnd)
      if tag notin result:
        result.add tag

func predicate(m: seq[Node]): (Matcher, seq[Node]) =
  ## predicate of a matcher (target node + filters)
  ## for runes that are not in the alphabet. All ASCII
  ## chars and expression chars are in the alphabet
  let n = m[0]
  case n.kind
  of reChar, reCharCI, reEOE:
    return (mFalse, @[])
  of reAny, reAnyNl:
    discard
  of reInSet:
    # set chars are in the alphabet
    if n.shorthands.len == 0:
      return (mFalse, @[])
    result[1].add n
  else:
    result[1].add n
  result[1].add m[1 .. ^1]
  result[0] = if result[1].len == 0: mTrue else: mPred

func ctxOf*(tests: set[CtxTest], r: Rune): int16 =
  ## previous char context; ``r`` is
  ## ``invalidRune`` at the start of the text
  if ctStart in tests and r == invalidRune:
    result = result or 1
  if ctStartNl in tests and (r == invalidRune or r == lineBreakRune):
    result = result or 2
  if ctWord in tests and r != invalidRune and isWord(r):
    result = result or 4
  if ctWordAscii in tests and r != invalidRune and isWordAscii(r):
    result = result or 8

func ctxTestsOf(transitions: Transitions): set[CtxTest] =
  for z in transitions.z:
    for n in z:
      case n.kind
      of reStart, reStartSym:
        result.incl ctStart
      of reStartSymML:
        result.incl ctStartNl
      of reWordBoundary, reNotWordBoundary:
        result.incl ctWord
      of reWordBoundaryAscii, reNotWordBoundaryAscii:
        result.incl ctWordAscii
      of reLookbehind, reNotLookbehind, reNotLookahead:
        raise newException(RegexError, "Unsupported assertion")
      else:
        discard

func firstNotIn(candidates: openArray[int32], syms: seq[int32]): Rune =
  for c in candidates:
    if c notin syms:
      return c.Rune
  doAssert false

type
  NfaTrans = object
    ## an NFA transition, precomputed
    target: int16
    isEoe: bool
    tags: seq[int16]
    assertions: seq[Node]
    matcher: int  ## index into the matchers
  Matchers = seq[seq[Node]]
    ## distinct target node + filters

func nfaTransitions(
  nfa: seq[Node],
  transitions: Transitions,
  matchers: var Matchers
): seq[seq[NfaTrans]] =
  result.setLen transitions.all.len
  for n in 0 .. transitions.all.len-1:
    for nti, nt in transitions.all[n].pairs:
      var tr = NfaTrans(
        target: nt,
        isEoe: nfa[nt].kind == reEOE,
        tags: tagsOf(transitions, n, nti))
      for z in zOf(transitions, n, nti):
        if z.kind in assertionKind:
          tr.assertions.add z
      let m = @[nfa[nt].bare] & filters(transitions, n, nti)
      tr.matcher = matchers.find(m)
      if tr.matcher == -1:
        matchers.add m
        tr.matcher = matchers.len-1
      result[n].add tr

func symClasses(
  syms: seq[int32],
  matchers: Matchers,
  transitions: Transitions
): seq[seq[int32]] =
  ## Group the alphabet chars that behave the same:
  ## same matchers results, and same results
  ## for the tests used by assertions
  var lookaheads: seq[int32]
  var hasAssertions = false
  for z in transitions.z:
    for n in z:
      if n.kind in assertionKind:
        hasAssertions = true
      if n.kind == reLookahead:
        lookaheads.add n.cp.int32
  var classes = initTable[seq[bool], int]()
  for sym in syms:
    var key: seq[bool]
    for m in matchers:
      var matched = true
      for n in m:
        if not match(n, sym.Rune):
          matched = false
          break
      key.add matched
    if hasAssertions:
      key.add sym == lineBreakRune.int32
      key.add isWord(sym.Rune)
      key.add isWordAscii(sym.Rune)
    for la in lookaheads:
      key.add sym == la
    if key notin classes:
      classes[key] = result.len
      result.add @[sym]
    else:
      result[classes[key]].add sym

func alphabet(nfa: seq[Node]): seq[int32] =
  ## Chars resolved at compile time: ASCII
  ## chars, and the expression chars
  var added = initHashSet[int32]()
  template add(c: Rune) =
    if c.int32 notin added:
      added.incl c.int32
      result.add c.int32
  for c in 0'i32 .. 128'i32:
    add c.Rune
  for n in nfa:
    case n.kind
    of reChar:
      add n.cp
    of reCharCI:
      add n.cp
      add n.cp.swapCase()
    of reInSet:
      for cp in n.cps:
        add cp
      for rg in n.ranges:
        for cp in rg:
          add cp
    else:
      discard

func tdfa*(
  nfa: seq[Node],
  transitions: Transitions,
  groupsCount: int,
  mode: TdfaMode
): Tdfa =
  result.mode = mode
  result.nTags = groupsCount*2 + int(mode == tmFind)
  let startTag = int16(result.nTags-1)
  result.ctxTests = ctxTestsOf(transitions)
  var syms = alphabet(nfa)
  # lookahead chars are compared to the next char
  for z in transitions.z:
    for n in z:
      if n.kind == reLookahead and n.cp.int32 notin syms:
        syms.add n.cp.int32
  result.alphabet = syms
  # runes not in the alphabet are only tested
  # by assertions for being word chars or not
  let
    wordRep = firstNotIn([0xE9'i32, 0x436, 0x3BB, 0x628], syms)
    nonWordRep = firstNotIn([0x2003'i32, 0x3000, 0xA0, 0x2028], syms)
    tests = result.ctxTests
  # a previous char for every context
  var ctxRep = initTable[int16, Rune]()
  for r in [-1'i32, lineBreakRune.int32, 'a'.ord.int32,
      wordRep.int32, ' '.ord.int32, nonWordRep.int32]:
    let ctx = ctxOf(tests, r.Rune)
    if ctx notin ctxRep:
      ctxRep[ctx] = r.Rune
  var statesIdx = initTable[seq[int16], int32]()
  var transIdx = initTable[TdfaTrans, int32]()
  var tagsIdx = initTable[seq[int16], int16]()
  var queue: seq[int32]
  template addState(ns: seq[int16], cx: int16): int32 =
    let stCtx = cx
    let key = @[stCtx] & ns
    if key notin statesIdx:
      if result.states.len >= maxStates:
        raise newException(RegexError,
          "The regex is too complex, it has too many states")
      statesIdx[key] = result.states.len.int32
      result.states.add TdfaState(nfaStates: ns, ctx: stCtx, eoe: -1)
      result.maxRegs = max(result.maxRegs, ns.len)
      queue.add (result.states.len-1).int32
    statesIdx[key]
  template addTags(tg: seq[int16]): int16 =
    let tgs = tg
    if tgs.len == 0:
      -1'i16
    else:
      if tgs notin tagsIdx:
        tagsIdx[tgs] = result.tags.len.int16
        result.tags.add tgs
      tagsIdx[tgs]
  template addTrans(tr: TdfaTrans): int32 =
    let tr2 = tr
    if tr2 notin transIdx:
      transIdx[tr2] = result.trans.len.int32
      result.trans.add tr2
    transIdx[tr2]
  # Step from state ``qi`` on the ``next`` char, taking
  # the NFA transitions for which ``cond`` is true.
  # ``next`` is ``invalidRune`` at the end of the text
  var matchers: Matchers
  let nfaTrans = nfaTransitions(nfa, transitions, matchers)
  let classes = symClasses(syms, matchers, transitions)
  template assertionsOk(tr: NfaTrans, prev, next: Rune): bool =
    var ok = true
    for z in tr.assertions:
      if not match(z, prev, next):
        ok = false
        break
    ok
  # Step from state ``qi`` on the ``next`` char, taking
  # the NFA transitions for which ``cond`` is true.
  # ``next`` is ``invalidRune`` at the end of the text
  template step(
    qi: int32, next: Rune, nextCtx: int16, cond: untyped
  ): int32 =
    let prev = ctxRep.getOrDefault(result.states[qi].ctx, invalidRune)
    let isEnd = next == invalidRune
    var ns: seq[int16]
    var ops: seq[TdfaOp]
    var accept: TdfaOp = (noAccept, -1'i16)
    block steps:
      for j, n0 in result.states[qi].nfaStates.pairs:
        let isRestart = n0 == restartNfa
        let n = if isRestart: 0'i16 else: n0
        let src = if isRestart: fresh else: j.int16
        for tr {.inject.} in nfaTrans[n]:
          if tr.assertions.len > 0 and not assertionsOk(tr, prev, next):
            continue
          if tr.isEoe:
            if isEnd or mode == tmFind:
              # lower priority NFA states are discarded
              var tags = tr.tags
              if isRestart:
                tags.add startTag
              accept = (src, addTags(tags))
              break steps
            continue
          if isEnd or tr.target in ns or not cond:
            continue
          ns.add tr.target
          if isRestart:
            ops.add (src, addTags(tr.tags & startTag))
          else:
            ops.add (src, addTags(tr.tags))
      # keep restarting until there is a match
      if not isEnd and restartNfa in result.states[qi].nfaStates:
        ns.add restartNfa
        ops.add (fresh, -1'i16)
    if ns.len == 0 and accept.src == noAccept:
      -1'i32
    else:
      let target = if ns.len == 0: -1'i32 else: addState(ns, nextCtx)
      addTrans(TdfaTrans(target: target, ops: ops, accept: accept))
  # initial states, by context
  let ns0 = if mode == tmFind: @[restartNfa] else: @[0'i16]
  result.initStates = newSeq[int32](16)
  for i in 0 .. 15:
    result.initStates[i] = -1
  for r in [-1'i32, lineBreakRune.int32, 'a'.ord.int32,
      wordRep.int32, ' '.ord.int32]:
    let ctx = ctxOf(tests, r.Rune)
    if result.initStates[ctx] == -1:
      result.initStates[ctx] = addState(ns0, ctx)
  # the initial state at the start of the text is state 0
  doAssert result.initStates[ctxOf(tests, invalidRune)] == 0
  # matchers results for every class
  var sym2class = initTable[int32, int]()
  var classMatches: seq[seq[bool]]
  for ci, cls in classes.pairs:
    for sym in cls:
      sym2class[sym] = ci
    var ms: seq[bool]
    for m in matchers:
      var matched = true
      for nd in m:
        if not match(nd, cls[0].Rune):
          matched = false
          break
      ms.add matched
    classMatches.add ms
  var matcherPreds: seq[(Matcher, seq[Node])]
  for m in matchers:
    matcherPreds.add predicate(m)
  let wordPred = @[Node(kind: reWord, cp: "#".toRune)]
  var qh = 0
  while qh < queue.len:
    let qi = queue[qh]
    inc qh
    for cls in classes:
      let sym = cls[0]
      let t = step(qi, sym.Rune, ctxOf(tests, sym.Rune),
        classMatches[sym2class[sym]][tr.matcher])
      if t != -1:
        for sym2 in cls:
          result.states[qi].syms.add (sym2, t)
    result.states[qi].eoe = step(qi, invalidRune, 0'i16, false)
    # predicates for runes not in the alphabet
    var preds: seq[seq[Node]]
    for n0 in result.states[qi].nfaStates:
      let n = if n0 == restartNfa: 0'i16 else: n0
      for tr in nfaTrans[n]:
        let (m, p) = matcherPreds[tr.matcher]
        if m == mPred and preds.find(p) == -1:
          preds.add p
    if ctWord in tests and preds.find(wordPred) == -1:
      preds.add wordPred
    if preds.len > maxPreds:
      raise newException(RegexError,
        "The regex is too complex, it has too many char classes")
    result.states[qi].preds = preds
    let wordIdx = preds.find(wordPred)
    for bits in 0 ..< (1 shl preds.len):
      let next = if wordIdx != -1 and (bits and (1 shl wordIdx)) != 0:
        wordRep
      else:
        nonWordRep
      var predOk: seq[bool]
      for (m, p) in matcherPreds:
        predOk.add(case m
          of mFalse: false
          of mTrue: true
          of mPred: (bits and (1 shl preds.find(p))) != 0)
      let t = step(qi, next, ctxOf(tests, next), predOk[tr.matcher])
      result.states[qi].predTrans.add t
  # runtime tables
  result.asciiTrans = newSeq[int32](result.states.len*128)
  for i in 0 .. result.asciiTrans.len-1:
    result.asciiTrans[i] = -1
  result.nonAsciiSyms.setLen result.states.len
  for qi, st in result.states.pairs:
    for (sym, t) in st.syms:
      if sym < 128:
        result.asciiTrans[qi*128 + sym] = t
      else:
        result.nonAsciiSyms[qi].add (sym, t)
    result.nonAsciiSyms[qi].sort()
  for sym in syms:
    if sym >= 128:
      result.nonAsciiAlphabet.add sym
  result.nonAsciiAlphabet.sort()
