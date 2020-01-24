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

proc dfa2*(nfa: seq[Node]): Dfa =
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

macro genClosureTable(
  q, c: int32,
  nt: int16,
  cs: static seq[Closure],
  closures: static seq[DfaClosure]
): untyped =
  #[
  case q:
  of 1.int32:
    case c:
    of 'A'.int32:
      case nt:
      of 2.int32:
        true
      else:
        false
    else: false
  else: false
  ]#
  doAssert cs.len > 0
  result = newStmtList()
  var caseStmtQ: seq[NimNode]
  caseStmtQ.add(q)
  for i, t in closures.pairs:
    var caseStmtC: seq[NimNode]
    caseStmtC.add(c)
    for c2, t2 in t:
      var caseStmtNt: seq[NimNode]
      caseStmtNt.add(nt)
      for s in cs[t2]:
        caseStmtNt.add(newTree(nnkOfBranch,
          newLit s.int16,
          newStmtList(
            newTree(nnkReturnStmt,
              ident"true"))))
      caseStmtNt.add(newTree(nnkElse,
        newStmtList(
          newTree(nnkReturnStmt,
            ident"false"))))
      caseStmtC.add(newTree(nnkOfBranch,
          newLit c2.int32,
          newStmtList(
            newTree(nnkCaseStmt,
              caseStmtNt))))
    caseStmtC.add(newTree(nnkElse,
        newStmtList(
          newTree(nnkReturnStmt,
            ident"false"))))
    caseStmtQ.add(newTree(nnkOfBranch,
          newLit i.int32,
          newStmtList(
            newTree(nnkCaseStmt,
              caseStmtC))))
  caseStmtQ.add(newTree(nnkElse,
    newStmtList(
      newTree(nnkReturnStmt,
        ident"false"))))
  result.add(newTree(nnkCaseStmt,
      caseStmtQ))
  when defined(reDumpMacro):
    echo "==== genClosureTable ===="
    echo repr(result)

proc inClosure(
  q, c: int32,
  nt: int16,
  cs: static seq[Closure],
  closures: static seq[DfaClosure]
): bool =
  genClosureTable(q, c, nt, cs, closures)

macro genSubmatch(
  q, n, c, cPrev, capt, captx, charIndex, matched, smB, capts: typed,
  transitions, transitionsZ: static TransitionsAll,
  zClosure: static ZclosureStates,
  cs, closures: typed
): untyped =
  result = newStmtList()
  var caseStmtN: seq[NimNode]
  caseStmtN.add(n)
  for i, t in transitions.pairs:
    var branchBodyN: seq[NimNode]
    for nti, nt in t.pairs:
      var inClosureBranch: seq[NimNode]
      if transitionsZ[i][nti] == -1'i16:
        inClosureBranch.add(newCall(
          bindSym"add",
          smB,
          newPar(
            newLit nt.int16,
            capt)))
      else:
        inClosureBranch.add(newAssignment(
          matched,
          ident"true"))
        inClosureBranch.add(newAssignment(
          captx,
          capt))
        for z in zClosure[transitionsZ[i][nti]]:
          case z.kind
          of groupKind:
            inClosureBranch.add(newCall(
              bindSym"add",
              capts,
              newTree(nnkObjConstr,
                bindSym"CaptNode",
                newTree(nnkExprColonExpr,
                  ident"parent",
                  captx),
                newTree(nnkExprColonExpr,
                  ident"bound",
                  charIndex),
                newTree(nnkExprColonExpr,
                  ident"idx",
                  newLit z.idx))))
            inClosureBranch.add(newAssignment(
              captx,
              newCall(
                bindSym"len",
                capts)))
            inClosureBranch.add(newCall(
              bindSym"dec",
              captx))
          of assertionKind:
            inClosureBranch.add(newTree(nnkIfStmt,
              newTree(nnkElifBranch,
                newTree(nnkPrefix,
                  ident"not",
                  newCall(
                    bindSym"match",
                    ident"z",
                    newCall(
                      bindSym"Rune",
                      cPrev),
                    newCall(
                      bindSym"Rune",
                      c))),
                newStmtList(newAssignment(
                  matched,
                  ident"false")))))
            # XXX add of matchTransitionKind: match(z, c.Rune)
          else:
            doAssert false
        #inClosureBranch.add(quote do:
        #  if `matched`:
        #    add(`smB`, (nti.int16, `captx`)))
        inClosureBranch.add(newTree(nnkIfStmt,
          newTree(nnkElifBranch,
            matched,
            newStmtList(newCall(
              bindSym"add",
              smB,
              newPar(
                newLit nt.int16,
                captx))))))
      doAssert inClosureBranch.len > 0
      branchBodyN.add(newTree(nnkIfStmt,
        newTree(nnkElifBranch,
          #quote do:
          #  inClosure(`n`, `c`, nt.int16, `csIdent`, `closuresIdent`),
          newCall(
            bindSym"inClosure",
            q,
            c,
            newLit nt.int16,
            cs,
            closures),
          newStmtList(
            inClosureBranch))))
    caseStmtN.add(newTree(nnkOfBranch,
      newLit i.int16,
      newStmtList(
        branchBodyN)))
  caseStmtN.add(newTree(nnkElse,
    newStmtList(
      newTree(nnkDiscardStmt,
        newEmptyNode()))))
  result.add(newTree(nnkCaseStmt,
    caseStmtN))
  when defined(reDumpMacro):
    echo "==== genSubmatch ===="
    echo repr(result)

proc submatch(
  smA, smB: var Submatches,
  capts: var Capts,
  regex: static Regex,
  i: int,
  q, cprev, c: int32
) {.inline.} =
  var captx: int
  var matched = true
  for n, capt in smA.items:
    genSubmatch(
      q, n, c, cPrev, capt, captx, i, matched, smB, capts,
      regex.transitions.all, regex.transitions.allZ,
      regex.transitions.z, regex.dfa.cs, regex.dfa.closures)
  swap(smA, smB)
  smB.setLen(0)

macro genSymMatchTable(
  q, qnext, c: int32,
  table: static seq[DfaRow]
): untyped =
  ## Generate symMatch transition table
  result = newStmtList()
  var caseStmtQ: seq[NimNode]
  caseStmtQ.add(q)
  var qBranches: seq[NimNode]
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
            newCall(bindSym"Rune", c)),
          newStmtList(
            newAssignment(
              qnext,
              newLit table[i][symDigit]))))
      of symWord:
        symIfs.add(newTree(nnkElifBranch,
          newCall(
            bindSym"isWord",
            newCall(bindSym"Rune", c)),
          newStmtList(
            newAssignment(
              qnext,
              newLit table[i][symWord]))))
      of symAny:
        symIfs.add(newTree(nnkElifBranch,
          newTree(nnkInfix,
            ident"!=",
            c,
            newLit lineBreakRune.int32),
          newStmtList(
            newAssignment(
              qnext,
              newLit table[i][symAny]))))
      of symAnyNl:
        symIfs.add(newTree(nnkElifBranch,
            ident"true",
            newStmtList(
              newAssignment(
                qnext,
                newLit table[i][symAnyNl]))))
      else:
        discard
    if symIfs.len > 0:
      symIfs.add(newTree(nnkElse,
        newStmtList(
          newAssignment(
            qnext,
            newLit -1'i32))))
      qBranches.add(newTree(nnkOfBranch,
        newLit i.int32,
        newStmtList(
          newTree(nnkIfStmt,
            symIfs))))
  if qBranches.len > 0:
    caseStmtQ.add(qBranches)
    caseStmtQ.add(newTree(nnkElse,
      newStmtList(
        newAssignment(
          qnext,
          newLit -1'i32))))
    result.add(newTree(nnkCaseStmt,
      caseStmtQ))
  when defined(reDumpMacro):
    echo "==== genSymMatchTable ===="
    echo repr(result)

macro genTable(
  q, qnext, c: int32,
  table: static seq[DfaRow]
): untyped =
  ## Generate transition table
  var caseStmtQ: seq[NimNode]
  caseStmtQ.add(q)
  for i, t in table.pairs:
    var caseStmtC: seq[NimNode]
    caseStmtC.add(c)
    for c2, t2 in t:
      caseStmtC.add(newTree(nnkOfBranch,
        newLit c2,
        newStmtList(
          newAssignment(
            qnext,
            newLit t2.int32))))
    caseStmtC.add(newTree(nnkElse,
      newStmtList(
        newAssignment(
          qnext,
          newLit -1'i32))))
    caseStmtQ.add(newTree(nnkOfBranch,
      newLit i.int32,
      newStmtList(
        newTree(nnkCaseStmt,
          caseStmtC))))
  caseStmtQ.add(newTree(nnkElse,
      newStmtList(
        newTree(nnkDiscardStmt,
          newEmptyNode()))))
  result = newStmtList(
    newTree(nnkCaseStmt,
      caseStmtQ))
  when defined(reDumpMacro):
    echo "==== genTable ===="
    echo repr(result)

# x10 times faster than matchImpl
proc matchImpl2*(
  text: string,
  regex: static Regex
): (bool, Captures) {.inline.} =
  var
    smA: Submatches
    smB: Submatches
    capts: Capts
    cPrev = -1'i32
    c: int32
    q = 0'i32
    qnext = 0'i32
    i = 0
  const regex2 = regex
  smA.add((0'i16, -1))
  for r in text:
    c = r.int32
    genTable(q, qnext, c, regex.dfa.table)
    if (qnext == -1'i32).unlikely:
      # XXX when no ascii mode
      genSymMatchTable(q, qnext, c, regex.dfa.table)
      if (qnext == -1'i32).unlikely:
        return (false, @[])
    submatch(smA, smB, capts, regex, i, q, cPrev, c)
    q = qnext
    cPrev = r.int32
    inc i
  result[0] = symEoe in regex2.dfa.table[q]
  if not result[0]:
    return
  if regex2.transitions.z.len == 0:
    return
  submatch(smA, smB, capts, regex, i, q, cPrev, symEoe)
  if smA.len == 0:
    result[0] = false
    return
  result[1] = constructSubmatches(capts, smA[0][1], regex2.groupsCount)
