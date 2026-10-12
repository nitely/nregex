## Static matcher: generates the TDFA as code,
## see ``tdfa`` and ``genTdfaLoop``

import std/unicode
import std/tables
import std/sets
import std/macros
import std/algorithm

import pkg/unicodeplus except isUpper, isLower
import pkg/unicodedb/properties

import common
import nodetype
import nodematch
import tdfa
import types

func newOfBranch(cs: seq[int32], body: NimNode): NimNode =
  ## Return ``of cs: body``; contiguous chars are
  ## merged into ranges
  result = newTree(nnkOfBranch)
  var i = 0
  while i < cs.len:
    var j = i
    while j+1 < cs.len and cs[j+1] == cs[j]+1:
      inc j
    if i == j:
      result.add newLit(cs[i])
    else:
      result.add newTree(nnkInfix,
        ident"..", newLit(cs[i]), newLit(cs[j]))
    i = j+1
  result.add body

func slowRuneAt(s: string, i: int): int {.noinline.} =
  ## Out-of-line ``fastRuneAt``, to keep the generated
  ## code small. Return the rune in the low 32 bits and
  ## its length in the high bits. Returning a tuple
  ## is slower, it goes through the stack. Not for JS
  var j = i
  var c: Rune
  fastRuneAt(s, j, c, true)
  result = ((j-i) shl 32) or c.int

func genNextChar(text, i, c: NimNode, isAscii: bool): NimNode =
  ## Decode the next rune into ``c``
  result = if isAscii:
    quote do:
      `c` = Rune(`text`[`i`])
      inc `i`
  else:
    quote do:
      when defined(js):
        fastRuneAt(`text`, `i`, `c`, true)
      else:
        if `text`[`i`].ord <= 127:
          `c` = Rune(`text`[`i`])
          inc `i`
        elif `text`[`i`].ord shr 5 == 0b110 and `i` < len(`text`)-1:
          `c` = Rune(
            (`text`[`i`].ord and 0b1_1111) shl 6 or
            (`text`[`i`+1].ord and 0b11_1111))
          `i` += 2
        else:
          let r = slowRuneAt(`text`, `i`)
          `c` = Rune(r and 0xffff_ffff)
          `i` += r shr 32

func genNodeMatch(n: Node, c: NimNode): NimNode =
  ## Generate code that returns whether
  ## rune ``c`` matches the node
  template call(f: untyped): NimNode =
    newCall(bindSym(astToStr(f)), c)
  template cInt: NimNode =
    newCall(ident"int32", c)
  case n.kind
  of reChar:
    infix(cInt, "==", newLit n.cp.int32)
  of reCharCI:
    infix(
      infix(cInt, "==", newLit n.cp.int32), "or",
      infix(cInt, "==", newLit n.cp.swapCase.int32))
  of reWord: call(isWord)
  of reNotAlphaNum: prefix(call(isWord), "not")
  of reDigit: newCall(bindSym"isDecimal", c)
  of reNotDigit: prefix(newCall(bindSym"isDecimal", c), "not")
  of reWhiteSpace: call(isWhiteSpaceUnicode)
  of reNotWhiteSpace: prefix(call(isWhiteSpaceUnicode), "not")
  of reWordAscii: call(isWordAscii)
  of reNotAlphaNumAscii: prefix(call(isWordAscii), "not")
  of reDigitAscii: call(isDigitAscii)
  of reNotDigitAscii: prefix(call(isDigitAscii), "not")
  of reWhiteSpaceAscii: call(isWhiteSpaceAscii)
  of reNotWhiteSpaceAscii: prefix(call(isWhiteSpaceAscii), "not")
  of reAny:
    infix(cInt, "!=", newLit lineBreakRune.int32)
  of reAnyNl:
    newLit true
  of reAnyAscii: call(isAnyAscii)
  of reAnyNlAscii:
    infix(call(isAnyAscii), "or",
      infix(cInt, "==", newLit lineBreakRune.int32))
  of reUCC, reNotUCC:
    let ccLit = newLit n.cc.int32
    let cond = newCall(bindSym"contains",
      newCall(bindSym"UnicodeCategorySet", ccLit),
      newCall(bindSym"unicodeCategory", c))
    if n.kind == reUCC: cond else: prefix(cond, "not")
  of reInSet, reNotSet:
    var cond = newLit false
    if n.cps.len > 0 or n.ranges.len > 0:
      var branch = newTree(nnkOfBranch)
      var cps: seq[int32]
      for cp in n.cps:
        cps.add cp.int32
      for cp in sorted(cps):
        branch.add newLit(cp)
      for rg in n.ranges:
        branch.add newTree(nnkInfix, ident"..",
          newLit rg.a.int32, newLit rg.b.int32)
      branch.add newLit(true)
      cond = newTree(nnkCaseStmt, cInt, branch,
        newTree(nnkElse, newLit false))
      cond = newPar(cond)
    for sh in n.shorthands:
      cond = infix(cond, "or", genNodeMatch(sh, c))
    if n.kind == reInSet: cond else: prefix(newPar(cond), "not")
  else:
    doAssert false, $n.kind
    newLit false

func tdfaOps(
  regex: Regex,
  ops: seq[TdfaOp],
  regs, pos: NimNode
): NimNode =
  ## Register operations of a TDFA transition.
  ## The registers of the i-th NFA state are
  ## ``regs[i*nTags ..< (i+1)*nTags]``. Registers
  ## are read before any of them is written
  result = newStmtList()
  let nTags = regex.tdfa.nTags
  if nTags == 0:
    return
  func tagsOf(regex: Regex, op: TdfaOp): seq[int16] =
    if op.tags != -1: regex.tdfa.tags[op.tags] else: @[]
  var reads = initTable[int, NimNode]()
  for i, op in ops.pairs:
    doAssert op.src != fresh
    if op.src == i:
      continue
    let tags = tagsOf(regex, op)
    for t in 0 ..< nTags:
      let r = op.src*nTags + t
      if t.int16 in tags or r in reads:
        continue
      let tmp = genSym(nskLet, "r")
      let rLit = newLit r
      reads[r] = tmp
      result.add(quote do:
        let `tmp` = `regs`[`rLit`])
  for i, op in ops.pairs:
    let tags = tagsOf(regex, op)
    for t in 0 ..< nTags:
      let w = newLit(i*nTags + t)
      if t.int16 in tags:
        result.add(quote do:
          `regs`[`w`] = `pos`)
      elif op.src != i:
        let v = reads[op.src*nTags + t]
        result.add(quote do:
          `regs`[`w`] = `v`)

macro genTdfaLoop(
  text: string,
  i, iPrev: int,
  q: int32,
  c: Rune,
  regs: untyped,
  captures: Captures,
  matched: bool,
  regex: static Regex,
  isAscii, noCaptures: static bool
): untyped =
  ## Generate a direct-coded TDFA, see ``genMatchLoop``.
  ## Every transition runs its register operations.
  ## Once done, ``matched`` and ``captures`` are set
  template tdfa: untyped = regex.tdfa
  let matchLoop = genSym(nskLabel, "matchLoop")
  # leave the loop on mismatch, so the caller can clean up
  let mismatch = quote do:
    `q` = -1'i32
    break `matchLoop`
  func transCode(
    regex: Regex, ti: int32, curr: int, q, regs, iPrev, mismatch: NimNode,
    noCaptures: bool
  ): NimNode =
    if ti == -1:
      return mismatch
    let tr = regex.tdfa.trans[ti]
    result = newStmtList()
    if not noCaptures:
      result.add tdfaOps(regex, tr.ops, regs, iPrev)
    if tr.target != curr:
      result.add newAssignment(q, newLit tr.target)
      result.add newTree(nnkBreakStmt, newEmptyNode())
    elif result.len == 0:
      result.add newTree(nnkDiscardStmt, newEmptyNode())
  var caseStmtQ = newTree(nnkCaseStmt, q)
  var caseStmtEoe = newTree(nnkCaseStmt, q)
  for si, st in tdfa.states.pairs:
    # group syms by transition
    var transSyms: seq[(int32, seq[int32])]
    for (sym, ti) in st.syms:
      var found = false
      for ts in transSyms.mitems:
        if ts[0] == ti:
          ts[1].add sym
          found = true
          break
      if not found:
        transSyms.add (ti, @[sym])
    var caseStmtC = newTree(nnkCaseStmt, quote do: int32(`c`))
    for (ti, syms) in transSyms:
      caseStmtC.add newOfBranch(sorted(syms),
        transCode(regex, ti, si, q, regs, iPrev, mismatch, noCaptures))
    # alphabet chars with no transition don't match;
    # the fallback is only for runes not in the alphabet
    var noTrans: seq[int32]
    for sym in tdfa.alphabet:
      var found = false
      for (sym2, _) in st.syms:
        if sym2 == sym:
          found = true
          break
      if not found:
        noTrans.add sym
    if noTrans.len > 0:
      caseStmtC.add newOfBranch(noTrans, mismatch)
    # runes not in the alphabet
    var fallback: NimNode
    if isAscii:
      # same as the DFA, non-alphabet bytes don't match
      fallback = mismatch
    elif st.preds.len == 0:
      fallback = transCode(regex, st.predTrans[0], si, q, regs, iPrev, mismatch, noCaptures)
    else:
      let bits = genSym(nskVar, "bits")
      fallback = newStmtList(quote do:
        var `bits` = 0)
      for pi, pred in st.preds.pairs:
        var cond = newLit true
        for n in pred:
          cond = infix(cond, "and", genNodeMatch(n, c))
        let bit = newLit(1 shl pi)
        fallback.add(quote do:
          if `cond`:
            `bits` = `bits` or `bit`)
      var caseStmtBits = newTree(nnkCaseStmt, bits)
      for b, ti in st.predTrans.pairs:
        caseStmtBits.add newTree(nnkOfBranch, newLit b,
          transCode(regex, ti, si, q, regs, iPrev, mismatch, noCaptures))
      caseStmtBits.add newTree(nnkElse, newTree(nnkDiscardStmt, newEmptyNode()))
      fallback.add caseStmtBits
    let matchChar = if caseStmtC.len > 1:
      caseStmtC.add newTree(nnkElse, fallback)
      caseStmtC
    else:
      fallback
    let nextChar = genNextChar(text, i, c, isAscii)
    let savePos = if noCaptures:
      newEmptyNode()
    else:
      newAssignment(iPrev, i)
    caseStmtQ.add newTree(nnkOfBranch, newLit si.int32, quote do:
      while true:
        if `i` >= len(`text`):
          break `matchLoop`
        `savePos`
        `nextChar`
        `matchChar`)
    # end of text
    if st.eoe != -1:
      let op = tdfa.trans[st.eoe].accept
      var body = newStmtList()
      if not noCaptures:
        # captures of the highest priority NFA state
        let nTags = tdfa.nTags
        let tags = if op.tags != -1: tdfa.tags[op.tags] else: @[]
        let groupsLit = newLit regex.groupsCount.int
        body.add(quote do:
          setLen(`captures`, `groupsLit`))
        var tagValues: seq[NimNode]
        for t in 0 ..< nTags:
          tagValues.add(if t.int16 in tags: i
            else: newTree(nnkBracketExpr, regs, newLit(op.src*nTags + t)))
        for g in 0 ..< regex.groupsCount.int:
          let gLit = newLit g
          let a = tagValues[g*2]
          let b = tagValues[g*2+1]
          let nonCaptureSym = bindSym"nonCapture"
          body.add(quote do:
            `captures`[`gLit`] = if `b` == -1: `nonCaptureSym` else: `a` .. `b`-1)
      body.add(quote do:
        `matched` = true)
      caseStmtEoe.add newTree(nnkOfBranch, newLit si.int32, body)
  caseStmtQ.add newTree(nnkElse, newTree(nnkDiscardStmt, newEmptyNode()))
  caseStmtEoe.add newTree(nnkElse, newTree(nnkDiscardStmt, newEmptyNode()))
  result = quote do:
    block `matchLoop`:
      while true:
        `caseStmtQ`
    `caseStmtEoe`
  when defined(reDumpMacro):
    echo "==== genTdfaLoop ===="
    echo repr(result)

func matchImpl*(
  text: string,
  regex: static Regex,
  m: var RegexMatch,
  flags: static MatchFlags,
  start = 0
): bool {.inline.} =
  ## Match the whole ``text`` from ``start``
  m.clear()
  result = false
  # workaround for VM registry limitation
  const
    noCaptures = mfNoCaptures in flags
    reFlags = regex.flags
    namedGroups {.used.} = regex.namedGroups
    maxRegs = regex.tdfa.maxRegs
    nTags = regex.tdfa.nTags
    ctxTests = regex.tdfa.ctxTests
    initStates = regex.tdfa.initStates
  var
    c: Rune
    q = 0'i32
    i = start
    iPrev = start
  when noCaptures:
    var regs: array[1, int]
  else:
    var regs: array[max(1, maxRegs*nTags), int]
    for r in regs.mitems:
      r = -1
  when ctxTests != {}:
    if start > 0:
      q = initStates[ctxOf(ctxTests, bwRuneAt(text, start-1))]
  genTdfaLoop(
    text, i, iPrev, q, c, regs, m.captures, result,
    regex, reAscii in reFlags, noCaptures)
  if not result:
    return
  when not noCaptures and namedGroups.len > 0:
    m.namedGroups = namedGroups
  m.boundaries = start .. i-1
