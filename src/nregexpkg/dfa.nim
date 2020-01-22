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
  Closure = HashSet[int16]
  DfaRow = Table[AlphabetSym, int32]
  DfaClosure = Table[AlphabetSym, int32]
  Dfa = object
    table: seq[DfaRow]
    cs: seq[Closure]
    closures: seq[DfaClosure]

const
  symEoe = -1'i32
  symWord = -3'i32
  symDigit = -4'i32
  symAny = -6'i32
  symAnyNl = -7'i32

proc createAlphabet(nfa: seq[Node]): seq[AlphabetSym] =
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
  assert toHashSet(result).len == result.len

proc delta(
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

proc dfa*(nfa: seq[Node]): Dfa =
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
  var qu: Table[Closure, int32]
  var quPos = 0'i32
  qu[q0] = quPos
  inc quPos
  while qw.len > 0:
    let qa = qw.popLast()
    for sym in alphabet:
      let s = delta(nfa, qa, sym)
      if s.len == 0:
        continue
      var t: HashSet[int16]
      closure(t, s)
      if t notin qu:
        qu[t] = quPos
        inc quPos
        qw.addFirst(t)
      if qu[qa] >= result.table.len-1:
        result.table.add(initTable[AlphabetSym, int32](2))
        result.closures.add(initTable[AlphabetSym, int32](2))
      result.table[qu[qa]][sym] = qu[t]
      result.cs.add(s)
      result.closures[qu[qa]][sym] = int32(result.cs.len-1)

type
  CaptNode = object
    parent: int
    bound: int
    idx: int
  Capts = seq[CaptNode]
  Captures* = seq[seq[Slice[int]]]

proc constructSubmatches(
  capts: Capts,
  capt: int,
  size: int
): Captures =
  template currGroup: untyped = result[capts[capt].idx]
  result.setLen(size)
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
  for c in result.mitems:
    c.reverse()

type
  NodeIdx = int16
  CaptIdx = int
  Submatches = seq[(NodeIdx, CaptIdx)]

proc submatch(
  smA, smB: var Submatches,
  capts: var Capts,
  transitions: Transitions,
  states: Closure,
  i: int,
  cprev, c: int32
) {.inline.} =
  var captx: int
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
          captx = capts.len-1
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
  smB.setLen(0)

type
  Regex* = object
    ## a compiled regular expression
    dfa*: Dfa
    transitions*: Transitions
    groupsCount*: int16
    namedGroups*: OrderedTable[string, int16]

# Order matters, subsets first
const syms = [
  symDigit,
  symWord,
  symAny,
  symAnyNl
]

# Slow match
template symMatch(table, q, c, cSym: untyped) =
  var matched = false
  for sym in syms:
    if sym notin table[q]:
      continue
    matched = case sym:
      of symDigit: c.isDecimal()
      of symWord: c.isWord()
      of symAny: c != lineBreakRune
      of symAnyNl: true
      else: false
    if matched:
      q = table[q][sym]
      cSym = sym
      break
  if not matched:
    q = -1'i32

proc matchImpl*(
  text: string,
  regex: Regex
): (bool, Captures) {.inline.} =
  #echo dfa
  var
    smA: Submatches
    smB: Submatches
    capts: Capts
    cPrev = -1'i32
    cSym: int32
    q = 0'i32
    qnext = 0'i32
    i = 0
  smA.add((0'i16, -1))
  #echo regex.dfa
  for c in text.runes:
    cSym = c.int32
    if (c.int32 in regex.dfa.table[q]).likely:
      qnext = regex.dfa.table[q][c.int32]
    else:
      symMatch(regex.dfa.table, qnext, c, cSym)
      if qnext == -1:
        return (false, @[])
    # XXX most of the slowness here
    #     comes from accessing the closure
    if regex.transitions.z.len > 0:
      submatch(
        smA, smB, capts, regex.transitions,
        regex.dfa.cs[regex.dfa.closures[q][cSym]], i, cPrev, c.int32)
    inc i
    cPrev = c.int32
    q = qnext
    #echo q
  result[0] = symEoe in regex.dfa.table[q]
  if not result[0]:
    return
  if regex.transitions.z.len == 0:
    return
  submatch(
    smA, smB, capts, regex.transitions,
    regex.dfa.cs[regex.dfa.closures[q][symEoe]], i, cPrev, -1'i32)
  if smA.len == 0:
    result[0] = false
    return
  result[1] = constructSubmatches(capts, smA[0][1], regex.groupsCount)

macro genSymMatchTable(
  q, qnext, c: int32,
  table: static seq[DfaRow]
): untyped =
  ## Generate symMatch transition table
  result = newStmtList()
  var caseStmtColumn: seq[NimNode]
  caseStmtColumn.add(ident"q")
  var columnBranches: seq[NimNode]
  for i, t in table.pairs:
    var symIfs: seq[NimNode]
    for sym in syms:
      if sym notin table[i]:
        continue
      case sym:
      of symDigit:
        symIfs.add(newTree(nnkElifBranch,
          newCall(
            bindSym"isDecimal",
            newCall(bindSym"Rune", ident"c")),
          newStmtList(
            newAssignment(
              ident"qnext",
              newLit(table[i][symDigit])))))
      of symWord:
        symIfs.add(newTree(nnkElifBranch,
          newCall(
            bindSym"isWord",
            newCall(bindSym"Rune", ident"c")),
          newStmtList(
            newAssignment(
              ident"qnext",
              newLit(table[i][symWord])))))
      of symAny:
        symIfs.add(newTree(nnkElifBranch,
          newTree(nnkInfix,
            ident"!=",
            ident"c",
            newLit(lineBreakRune.int32)),
          newStmtList(
            newAssignment(
              ident"qnext",
              newLit(table[i][symAny])))))
      of symAnyNl:
        symIfs.add(newTree(nnkElifBranch,
            ident"true",
            newStmtList(
              newAssignment(
                ident"qnext",
                newLit(table[i][symAnyNl])))))
      else:
        discard
    if symIfs.len > 0:
      symIfs.add(newTree(nnkElse,
        newStmtList(
          newAssignment(
            ident"qnext",
            newLit(-1'i32)))))
      columnBranches.add(newTree(nnkOfBranch,
        newLit(i.int32),
        newStmtList(
          newTree(nnkIfStmt,
            symIfs))))
  if columnBranches.len > 0:
    caseStmtColumn.add(columnBranches)
    caseStmtColumn.add(newTree(nnkElse,
      newStmtList(
        newAssignment(
          ident"qnext",
          newLit(-1'i32)))))
    result.add(newTree(nnkCaseStmt,
      caseStmtColumn))
  #echo repr(result)

macro genTable(
  q, qnext, c: int32,
  table: static seq[DfaRow]
): untyped =
  ## Generate transition table
  var caseStmtColumn: seq[NimNode]
  caseStmtColumn.add(ident"q")
  for i, t in table.pairs:
    var caseStmtRow: seq[NimNode]
    caseStmtRow.add(ident"c")
    for c2, t2 in t:
      caseStmtRow.add(newTree(nnkOfBranch,
        newLit(c2),
        newStmtList(
          newAssignment(
            ident"qnext",
            newLit(t2)))))
    caseStmtRow.add(newTree(nnkElse,
      newStmtList(
        newAssignment(
          ident"qnext",
          newLit(-1'i32)))))
    caseStmtColumn.add(newTree(nnkOfBranch,
      newLit(i.int32),
      newStmtList(
        newTree(nnkCaseStmt,
          caseStmtRow))))
  caseStmtColumn.add(newTree(nnkElse,
      newStmtList(
        newTree(nnkDiscardStmt,
          newEmptyNode()))))
  result = newStmtList(
    newTree(nnkCaseStmt, caseStmtColumn))
  #echo repr(result)

# x10 times faster than matchImpl
proc matchImpl2*(
  text: string,
  regex: static Regex
): bool {.inline.} =
  var
    q = 0'i32
    qnext = 0'i32
    c: int32
  for r in text:
    c = r.int32
    genTable(q, qnext, c, regex.dfa.table)
    if (qnext == -1'i32).unlikely:
      # XXX when no ascii mode
      genSymMatchTable(q, qnext, c, regex.dfa.table)
      if (qnext == -1'i32).unlikely:
        return false
    q = qnext
  return symEoe in regex.dfa.table[q]
