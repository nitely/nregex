import unicode
import sets
import tables
import deques
import algorithm
import macros

import unicodeplus except isUpper, isLower

import nodematch
import nodetype
import common
import nfa

type
  AlphabetSym = int32
  Closure* = HashSet[int16]
  DfaRow* = Table[AlphabetSym, int32]
  DfaClosure* = Table[AlphabetSym, int32]
  Dfa* = object
    table*: seq[DfaRow]
    cs*: seq[Closure]
    closures*: seq[DfaClosure]

const
  symEoe* = -1'i32
  symWord* = -3'i32
  symDigit* = -4'i32
  symAny* = -6'i32
  symAnyNl* = -7'i32

func createAlphabet(nfa: seq[Node]): seq[AlphabetSym] =
  var inAlphabet: HashSet[AlphabetSym]
  # speedup ascii matching
  for c in 0 .. 128:
    result.add(c.int32)
    inAlphabet.incl(c.int32)
  # special symbols
  result.add(symEoe)
  result.add(symWord)
  result.add(symDigit)
  result.add(symAny)
  result.add(symAnyNl)
  # expression chars
  for n in nfa:
    case n.kind
    of reChar:
      if n.cp.int32 notin inAlphabet:
        result.add(n.cp.int32)
        inAlphabet.incl(n.cp.int32)
    of reCharCI:
      if n.cp.int32 notin inAlphabet:
        result.add(n.cp.int32)
        inAlphabet.incl(n.cp.int32)
      let cp2 = n.cp.swapCase()
      if cp2.int32 notin inAlphabet:
        result.add(cp2.int32)
        inAlphabet.incl(cp2.int32)
    of reInSet:
      for cp in n.cps:
        if cp.int32 notin inAlphabet:
          result.add(cp.int32)
          inAlphabet.incl(cp.int32)
      for rg in n.ranges:
        for cp in rg:
          if cp.int32 notin inAlphabet:
            result.add(cp.int32)
            inAlphabet.incl(cp.int32)
    else:
      discard
  assert result.toHashSet.len == result.len

func delta(
  nfa: seq[Node],
  states: Closure,
  sym: AlphabetSym
): Closure =
  result = initHashSet[int16](2)
  if sym > -1:
    for s in states:
      if match(nfa[s], sym.Rune):
        result.incl(s)
  else:
    # XXX this will add every sym for reAny, but we should only add symAny
    let kinds = case sym
      of symEoe: {reEoe}
      of symWord: {reAnyNl, reAny, reWord}
      of symDigit: {reAnyNl, reAny, reWord, reDigit}
      of symAny: {reAnyNl, reAny}
      of symAnyNl: {reAnyNl}
      else: {}
    for s in states:
      if nfa[s].kind in kinds:
        result.incl(s)
      if nfa[s].kind == reInSet:
        for sh in nfa[s].shorthands:
          if sh.kind in kinds:
            result.incl(s)
            break

func dfa*(nfa: seq[Node]): Dfa =
  ## Powerset construction
  template closure(result, states) =
    for s in states:
      for sn in nfa[s].next:
        result.incl(sn)
  let alphabet = createAlphabet(nfa)
  let n0 = 0
  var q0: Closure
  closure(q0, [n0])
  var qw = initDeque[Closure]()
  qw.addFirst(q0)
  var qu = initTable[Closure, int32]()
  var quPos = 0'i32
  qu[q0] = quPos
  inc quPos
  result.table.add(initTable[AlphabetSym, int32](2))
  result.closures.add(initTable[AlphabetSym, int32](2))
  var t = initHashSet[int16]()
  var csRev = initTable[Closure, int32]()
  while qw.len > 0:
    let qa = qw.popLast()
    for sym in alphabet:
      let s = delta(nfa, qa, sym)
      if s.len == 0:
        continue
      t.clear()
      closure(t, s)
      if t notin qu:
        qu[t] = quPos
        inc quPos
        qw.addFirst(t)
        result.table.add(initTable[AlphabetSym, int32](2))
        result.closures.add(initTable[AlphabetSym, int32](2))
      result.table[qu[qa]][sym] = qu[t]
      if s in csRev:
        result.closures[qu[qa]][sym] = csRev[s]
      else:
        assert s notin result.cs
        result.closures[qu[qa]][sym] = result.cs.len.int32
        csRev[s] = result.cs.len.int32
        result.cs.add(s)

func xF(dfa: Dfa): HashSet[int32] =
  ## return all final states
  for i, t in dfa.table.pairs:
    if symEoe in t:
      result.incl(i.int32)
  doAssert result.len > 0

func xQ(dfa: Dfa): HashSet[int32] =
  ## return all states
  for i in 0'i32 .. (dfa.table.len-1).int32:
    result.incl(i)

func delta(
  dfa: Dfa,
  s: HashSet[int32],
  c: AlphabetSym
): HashSet[int32] =
  ## return set of states that can reach `s` on `c`
  for i, t in dfa.table.pairs:
    if c in t and t[c] in s:
      result.incl(i.int32)

proc partition(r, i: HashSet[int32]): (HashSet[int32], HashSet[int32]) =
  ## partition r into r1 and r2, such as r1 is the intersection
  ## of r and i, and r2 is r - such intersection
  for x in r:
    if x in i:
      result[0].incl(x)
    else:
      result[1].incl(x)

# unoptimized
func minimize*(
  dfa: Dfa,
  alphabet: seq[AlphabetSym]
): Dfa =
  ## Hopcroft
  let f = dfa.xF()
  let q = dfa.xQ()
  var w: seq[HashSet[int32]]
  w.add(f)
  w.add(q - f)
  var p: seq[HashSet[int32]]
  p.add(f)
  p.add(q - f)
  while w.len > 0:
    let s = w.pop()
    for c in alphabet:
      let i = delta(dfa, s, c)
      var pcopy = p
      for r in pcopy:
        if (r - i).len == 0:  # is R a subset of I
          continue
        if (i - r).len == i.len: # the intersection of R and I is empty
          continue
        let (r1, r2) = partition(r, i)
        assert p.find(r) > -1
        p[p.find(r)] = r1  # XXX for ri, r in p.pairs
        p.add(r2)
        if r in w:
          assert w.find(r) > -1
          w[w.find(r)] = r1
          w.add(r2)
        elif r1.len <= r2.len:
          w.add(r1)
        else:
          w.add(r2)
  assert p.len <= dfa.table.len, "not a min DFA, wtf?"
  # map DFA states to min-DFA states
  var statesMap = newSeq[int32](dfa.table.len)
  for i in 0 .. statesMap.len-1:
    statesMap[i] = -1
  for ri, r in p.pairs:
    for q in r:
      assert statesMap[q] == -1
      statesMap[q] = ri.int32
  result.table.setLen(p.len)
  result.closures.setLen(p.len)
  var closure = initHashSet[int16](2)
  var qnext: int32
  for ri, r in p.pairs:
    result.table[ri] = initTable[AlphabetSym, int32](2)
    result.closures[ri] = initTable[AlphabetSym, int32](2)
    for c in alphabet:  # XXX iterate dfa.table[q] instead
      qnext = -1'i32
      closure.clear()
      for q in r:  # r = new closure
        if c notin dfa.table[q]:
          continue
        assert qnext == -1 or qnext == dfa.table[q][c]
        qnext = dfa.table[q][c]
        closure.incl(dfa.cs[dfa.closures[q][c]])
      if qnext == -1:
        assert closure.len == 0
        continue
      assert closure.len > 0
      assert c notin result.table[ri]
      result.table[ri][c] = statesMap[qnext]
      # XXX massive duplication, closure is likely already in cs
      result.cs.add(closure)
      result.closures[ri][c] = (result.cs.len-1).int32

type
  CaptNode* = object
    parent*: int
    bound*: int
    idx*: int
  Capts* = seq[CaptNode]
  Captures* = seq[seq[Slice[int]]]

func constructSubmatches*(
  captures: var Captures,
  capts: Capts,
  capt: int,
  size: int
) =
  template currGroup: untyped = captures[capts[capt].idx]
  captures.setLen(size)
  for i in 0 .. captures.len-1:
    captures[i].setLen(0)
  if capts.len == 0:
    return
  var capt = capt
  while capt != -1:
    if currGroup.len == 0:
      currGroup.add(-2 .. -2)
    if currGroup[^1].a != -2:
      currGroup.add(-2 .. -2)
    if currGroup[^1].b == -2:
      currGroup[^1].b = capts[capt].bound-1
    else:
      currGroup[^1].a = capts[capt].bound
    capt = capts[capt].parent
  for c in captures.mitems:
    c.reverse()

type
  NodeIdx = int16
  CaptIdx = int32
  Submatches* = seq[(NodeIdx, CaptIdx)]
    ## Parallel states would be a better name

func submatch(
  smA, smB: var Submatches,
  capts: var Capts,
  transitions: Transitions,
  states: Closure,
  i: int,
  cprev, c: int32
) {.inline.} =
  smB.setLen(0)
  var captx: int32
  var matched = true
  for n, capt in smA.items:
    for nti, nt in transitions.all[n].pairs:
      if nt notin states:
        continue
      if transitions.allZ[n][nti] == -1'i16:
        smB.add((nt, capt))
        continue
      matched = true
      captx = capt
      for z in transitions.z[transitions.allZ[n][nti]]:
        if not matched:
          break
        case z.kind
        of groupKind:
          capts.add(CaptNode(
            parent: captx,
            bound: i,
            idx: z.idx))
          captx = (capts.len-1'i32).int32
        of assertionKind:
          matched = match(z, cprev.Rune, c.Rune)
        of matchTransitionKind:
          matched = match(z, c.Rune)
        else:
          assert false
          discard
      if matched:
        smB.add((nt, captx))
  swap(smA, smB)

type
  RegexFlag* = enum
    reAscii
  Regex* = object
    ## a compiled regular expression
    dfa*: Dfa
    transitions*: Transitions
    groupsCount*: int16
    namedGroups*: OrderedTable[string, int16]
    flags*: set[RegexFlag]
  MatchFlag* = enum
    mfShortestMatch
    mfLongestMatch
    mfNoCaptures
  MatchFlags* = set[MatchFlag]
  RegexMatch* = object
    ## result from matching operations
    captures*: Captures
    namedGroups*: OrderedTable[string, int16]
    boundaries*: Slice[int]

func clear*(m: var RegexMatch) {.inline.} =
  if m.captures.len > 0:
    m.captures.setLen(0)
  if m.namedGroups.len > 0:
    m.namedGroups.clear()
  m.boundaries = 0 .. -1

# Order matters, subsets first
const syms* = [
  symDigit,
  symWord,
  symAny,
  symAnyNl
]

# Slow match
func symMatch(
  q: var int32,
  c: Rune,
  cSym: var int32,
  regex: Regex
) {.inline.} =
  var matched = false
  for sym in syms:
    if sym notin regex.dfa.table[q]:
      continue
    matched = case sym:
      of symDigit: c.isDecimal()
      of symWord: c.isWord()
      of symAny: c != lineBreakRune
      of symAnyNl: true
      else: false
    if matched:
      q = regex.dfa.table[q][sym]
      cSym = sym
      break
  if not matched:
    q = -1'i32

# Can't return early because of boundaries
template longestMatchEnter() {.dirty.} =
  if symEoe in regex.dfa.table[q]:
    matchedLong = true
    iPrevLong = iPrev
    if regex.transitions.z.len > 0:
      submatch(
        smA, smB, capts, regex.transitions,
        regex.dfa.cs[regex.dfa.closures[q][symEoe]], iPrev, cPrev, c.int32)
      if smA.len > 0:
        captLong = smA[0][1]
      swap(smA, smB)

template longestMatchExit() {.dirty.} =
  result = matchedLong
  if regex.transitions.z.len > 0:
    constructSubmatches(m.captures, capts, captLong, regex.groupsCount)
    if regex.namedGroups.len > 0:
      m.namedGroups = regex.namedGroups
  m.boundaries = start .. iPrevLong-1
  return

template shortestMatch() {.dirty.} =
  if symEoe in regex.dfa.table[q]:
    if regex.transitions.z.len > 0:
      submatch(
        smA, smB, capts, regex.transitions,
        regex.dfa.cs[regex.dfa.closures[q][symEoe]], iPrev, cPrev, c.int32)
      if smA.len > 0:
        result = true
        return
      swap(smA, smB)
    else:
      result = true
      return

func matchImpl*(
  text: string,
  regex: Regex,
  m: var RegexMatch,
  flags: static MatchFlags,
  start = 0
): bool {.inline.} =
  #echo dfa
  m.clear()
  result = false
  let asciiMode = reAscii in regex.flags
  var
    smA: Submatches
    smB: Submatches
    capts: Capts
    c: Rune
    cPrev = -1'i32
    cSym: int32
    q = 0'i32
    qnext = 0'i32
    i = start
    iPrev = start
    # Long match
    matchedLong {.used.} = false
    captLong {.used.} = -1
    iPrevLong {.used.} = start
  if regex.transitions.z.len > 0:
    smA.add((0'i16, -1'i32))
  #echo regex.dfa
  while i < len(text):
    if not asciiMode:
      fastRuneAt(text, i, c, true)
    else:
      c = Rune(text[i])
      inc i
    when mfShortestMatch in flags:
      shortestMatch()
    when mfLongestMatch in flags:
      longestMatchEnter()
    cSym = c.int32
    if (c.int32 in regex.dfa.table[q]).likely:
      qnext = regex.dfa.table[q][c.int32]
    else:
      if not asciiMode:
        symMatch(qnext, c, cSym, regex)
      if qnext == -1 or asciiMode:
        when mfLongestMatch in flags:
          longestMatchExit()
        else:
          return
    if regex.transitions.z.len > 0:
      submatch(
        smA, smB, capts, regex.transitions,
        regex.dfa.cs[regex.dfa.closures[q][cSym]], iPrev, cPrev, c.int32)
    iPrev = i
    cPrev = c.int32
    q = qnext
    #echo q
  result = symEoe in regex.dfa.table[q]
  if not result:
    when mfLongestMatch in flags:
      longestMatchExit()
    return
  if regex.transitions.z.len > 0:
    submatch(
      smA, smB, capts, regex.transitions,
      regex.dfa.cs[regex.dfa.closures[q][symEoe]], iPrev, cPrev, -1'i32)
    if smA.len == 0:  # XXX is this possible?
      when mfLongestMatch in flags:
        longestMatchExit()
      result = false
      return
    constructSubmatches(m.captures, capts, smA[0][1], regex.groupsCount)
    if regex.namedGroups.len > 0:
      m.namedGroups = regex.namedGroups
  m.boundaries = start .. iPrev-1