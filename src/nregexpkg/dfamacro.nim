import sets
import tables
import macros

import unicodeplus except isUpper, isLower

import common
import nodetype
import nodematch
import nfa
import dfa

macro genClosureTable(
  qt: int32,
  nt: int16,
  regex: static Regex
): untyped =
  #[
  case qt:  # curr closure
  of 1.int32:
    case nt:  # next state
    of 2.int32:
      true
    else:
      false
  else: false
  ]#
  doAssert regex.dfa.cs.len > 0
  result = newStmtList()
  var caseStmtQ: seq[NimNode]
  caseStmtQ.add(qt)
  for i, t2 in regex.dfa.cs.pairs:
    #if t2.len == 0:  # ?
    #  continue
    var caseStmtNt: seq[NimNode]
    caseStmtNt.add(nt)
    for s in t2:
      caseStmtNt.add(newTree(nnkOfBranch,
        newLit s,
        quote do:
          return true))
    caseStmtNt.add(newTree(nnkElse,
      quote do:
        return false))
    caseStmtQ.add(newTree(nnkOfBranch,
      newLit i.int32,
      newStmtList(
        newTree(nnkCaseStmt, caseStmtNt))))
  caseStmtQ.add(newTree(nnkElse,
    quote do:
      return false))
  result.add(newTree(nnkCaseStmt, caseStmtQ))
  when defined(reDumpMacro):
    echo "==== genClosureTable ===="
    echo repr(result)

proc inClosure(
  qt: int32,
  nt: int16,
  regex: static Regex
): bool =
  genClosureTable(qt, nt, regex)

macro genSubmatch(
  n, c, qt, cPrev, capt, captx, charIndex, matched, smB, capts: typed,
  regex: static Regex
): untyped =
  result = newStmtList()
  var caseStmtN: seq[NimNode]
  caseStmtN.add(n)
  for i, t in regex.transitions.all.pairs:
    if t.len == 0:  # end state
      continue
    var branchBodyN: seq[NimNode]
    for nti, nt in t.pairs:
      let ntLit = newLit nt
      var inClosureBranch: seq[NimNode]
      if regex.transitions.allZ[i][nti] == -1'i16:
        inClosureBranch.add(quote do:
          add(`smB`, (`ntLit`, `capt`)))
      else:
        inClosureBranch.add(quote do:
          `matched` = true
          `captx` = `capt`)
        for z in regex.transitions.z[regex.transitions.allZ[i][nti]]:
          case z.kind
          of groupKind:
            let zIdx = newLit z.idx
            inClosureBranch.add(quote do:
              add(`capts`, CaptNode(parent: `captx`, bound: `charIndex`, idx: `zIdx`))
              `captx` = len(`capts`) - 1)
          of assertionKind:
            # https://github.com/nim-lang/Nim/issues/13266
            #let zLit = newLit z
            inClosureBranch.add(quote do:
              `matched` = match(`z`, Rune(`cPrev`), Rune(`c`)))
          of matchTransitionKind:
            #let zLit = newLit z
            inClosureBranch.add(quote do:
              `matched` = match(`z`, Rune(`c`)))
          else:
            doAssert false
        inClosureBranch.add(quote do:
          if `matched`:
            add(`smB`, (`ntLit`, `captx`)))
      doAssert inClosureBranch.len > 0
      let inClosureBranchStmt = newStmtList inClosureBranch
      branchBodyN.add(quote do:
        if inClosure(`qt`, `ntLit`, regex):
          `inClosureBranchStmt`)
    doAssert branchBodyN.len > 0
    caseStmtN.add(newTree(nnkOfBranch,
      newLit i.int16,
      newStmtList(
        branchBodyN)))
  caseStmtN.add(newTree(nnkElse,
    newStmtList(
      newTree(nnkDiscardStmt, newEmptyNode()))))
  result.add(newTree(nnkCaseStmt, caseStmtN))
  when defined(reDumpMacro):
    echo "==== genSubmatch ===="
    echo repr(result)

proc submatch(
  smA, smB: var Submatches,
  capts: var Capts,
  regex: static Regex,
  i: int,
  qt, cprev, c: int32
) {.inline.} =
  var captx: int
  var matched = true
  for n, capt in smA.items:
    genSubmatch(
      n, c, qt, cPrev, capt, captx, i, matched, smB, capts, regex)
  swap(smA, smB)
  smB.setLen(0)

macro genEoeTable(
  matched: bool,
  q, qt: int32,
  regex: static Regex
): untyped =
  ## Generate Eoe table
  result = newStmtList()
  var caseStmtQ: seq[NimNode]
  caseStmtQ.add(q)
  for i, t in regex.dfa.table.pairs:
    if symEoe in t:
      let trueLit = newLit true
      let qtLit = newLit regex.dfa.closures[i][symEoe]
      caseStmtQ.add(newTree(nnkOfBranch,
        newLit i.int32,
        quote do:
          `matched` = `trueLit`
          `qt` = `qtLit`))
  doAssert caseStmtQ.len > 1
  let falseLit = newLit false
  let qtLit = newLit -1'i32
  caseStmtQ.add(newTree(nnkElse,
    quote do:
      `matched` = `falseLit`
      `qt` = `qtLit`))
  result.add(
    newTree(nnkCaseStmt, caseStmtQ))
  when defined(reDumpMacro):
    echo "==== genEoeTable ===="
    echo repr(result)

macro genSymMatchTable(
  q, qt, c: int32,
  regex: static Regex
): untyped =
  ## Generate symMatch transition table
  result = newStmtList()
  var caseStmtQ: seq[NimNode]
  caseStmtQ.add(q)
  var qBranches: seq[NimNode]
  for i, t in regex.dfa.table.pairs:
    var symIfs: seq[NimNode]
    for sym in syms:
      if sym notin regex.dfa.table[i]:
        continue
      case sym:
      of symDigit:
        let tLit = newLit regex.dfa.table[i][symDigit]
        let qtLit = newLit regex.dfa.closures[i][symDigit]
        symIfs.add(newTree(nnkElifBranch,
          quote do:
            isDecimal(Rune(`c`)),
          quote do:
            `q` = `tLit`
            `qt` = `qtLit`))
      of symWord:
        let tLit = newLit regex.dfa.table[i][symWord]
        let qtLit = newLit regex.dfa.closures[i][symWord]
        symIfs.add(newTree(nnkElifBranch,
          quote do:
            isWord(Rune(`c`)),
          quote do:
            `q` = `tLit`
            `qt` = `qtLit`))
      of symAny:
        let lineBreakLit = newLit lineBreakRune.int32
        let tLit = newLit regex.dfa.table[i][symAny]
        let qtLit = newLit regex.dfa.closures[i][symAny]
        symIfs.add(newTree(nnkElifBranch,
          quote do:
            `c` != `lineBreakLit`,
          quote do:
            `q` = `tLit`
            `qt` = `qtLit`))
      of symAnyNl:
        let tLit = newLit regex.dfa.table[i][symAnyNl]
        let qtLit = newLit regex.dfa.closures[i][symAnyNl]
        symIfs.add(newTree(nnkElifBranch,
          quote do:
            true,
          quote do:
            `q` = `tLit`
            `qt` = `qtLit`))
      else:
        doAssert false
        discard
    if symIfs.len > 0:
      let tLit = newLit -1'i32
      symIfs.add(newTree(nnkElse,
        quote do:
          `q` = `tLit`
          `qt` = `tLit`))
      qBranches.add(newTree(nnkOfBranch,
        newLit i.int32,
        newStmtList(
          newTree(nnkIfStmt, symIfs))))
  if qBranches.len > 0:
    let tLit = newLit -1'i32
    caseStmtQ.add(qBranches)
    caseStmtQ.add(newTree(nnkElse,
      quote do:
        `q` = `tLit`
        `qt` = `tLit`))
    result.add(newTree(nnkCaseStmt, caseStmtQ))
  when defined(reDumpMacro):
    echo "==== genSymMatchTable ===="
    echo repr(result)

macro genTable(
  q, qt, c: int32,
  regex: static Regex
): untyped =
  ## Generate transition table
  var caseStmtQ: seq[NimNode]
  caseStmtQ.add(q)
  for i, t in regex.dfa.table.pairs:
    var caseStmtC: seq[NimNode]
    caseStmtC.add(c)
    for c2, t2 in t:
      let t2Lit = newLit t2.int32
      let qtLit = newLit regex.dfa.closures[i][c2]
      caseStmtC.add(newTree(nnkOfBranch,
        newLit c2,
        quote do:
          `q` = `t2Lit`
          `qt` = `qtLit`))
    let t2Lit = newLit -1'i32
    caseStmtC.add(newTree(nnkElse,
      quote do:
        `q` = `t2Lit`
        `qt` = `t2Lit`))
    caseStmtQ.add(newTree(nnkOfBranch,
      newLit i.int32,
      newStmtList(
        newTree(nnkCaseStmt, caseStmtC))))
  caseStmtQ.add(newTree(nnkElse,
    newStmtList(
      newTree(nnkDiscardStmt, newEmptyNode()))))
  result = newStmtList(
    newTree(nnkCaseStmt, caseStmtQ))
  when defined(reDumpMacro):
    echo "==== genTable ===="
    echo repr(result)

# x10 times faster than matchImpl
proc matchImpl*(
  text: string,
  regex: static Regex,
  captures: var Captures,
  flags: static MatchFlags,
  start = 0
): bool {.inline.} =
  result = false
  var
    smA: Submatches
    smB {.used.}: Submatches
    capts {.used.}: Capts
    cPrev = -1'i32
    c: int32
    q = 0'i32
    qOld = q
    qt = q
    i = 0
  # workaround for https://github.com/nim-lang/Nim/issues/13252
  const hasTransionsZ = regex.transitions.z.len > 0
  const groupCount {.used.} = regex.groupsCount
  smA.add((0'i16, -1))
  for r in text.runes:
    c = r.int32
    qOld = q
    genTable(q, qt, c, regex)
    if (q == -1'i32).unlikely:
      # XXX when no ascii mode
      q = qOld
      genSymMatchTable(q, qt, c, regex)
      if (q == -1'i32).unlikely:
        return
    when hasTransionsZ:
      submatch(smA, smB, capts, regex, i, qt, cPrev, c)
    cPrev = r.int32
    inc i
  genEoeTable(result, q, qt, regex)
  when hasTransionsZ:
    if not result:
      return
    submatch(smA, smB, capts, regex, i, qt, cPrev, symEoe)
    if smA.len == 0:
      result = false
      return
    constructSubmatches(captures, capts, smA[0][1], groupCount)
