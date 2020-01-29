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
  q, cSym: int32,
  nt: int16,
  regex: static Regex
): untyped =
  #[
  case q:  # curr state
  of 1.int32:
    case cSym:  # curr char or sym
    of 'A'.int32:
      case nt:  # next state
      of 2.int32:
        true
      else:
        false
    else: false
  else: false
  ]#
  doAssert regex.dfa.cs.len > 0
  result = newStmtList()
  var caseStmtQ: seq[NimNode]
  caseStmtQ.add(q)
  for i, t in regex.dfa.closures.pairs:
    if t.len == 0:  # end state
      continue
    var caseStmtC: seq[NimNode]
    caseStmtC.add(cSym)
    for c2, t2 in t:
      var caseStmtNt: seq[NimNode]
      caseStmtNt.add(nt)
      for s in regex.dfa.cs[t2]:
        caseStmtNt.add(newTree(nnkOfBranch,
          newLit s.int16,
          quote do:
            return true))
      caseStmtNt.add(newTree(nnkElse,
        quote do:
          return false))
      caseStmtC.add(newTree(nnkOfBranch,
        newLit c2.int32,
        newStmtList(
          newTree(nnkCaseStmt, caseStmtNt))))
    caseStmtC.add(newTree(nnkElse,
      quote do:
        return false))
    caseStmtQ.add(newTree(nnkOfBranch,
      newLit i.int32,
      newStmtList(
        newTree(nnkCaseStmt, caseStmtC))))
  caseStmtQ.add(newTree(nnkElse,
    quote do:
      return false))
  result.add(newTree(nnkCaseStmt, caseStmtQ))
  when defined(reDumpMacro):
    echo "==== genClosureTable ===="
    echo repr(result)

proc inClosure(
  q, cSym: int32,
  nt: int16,
  regex: static Regex
): bool =
  genClosureTable(q, cSym, nt, regex)

macro genSubmatch(
  q, n, c, cSym, cPrev, capt, captx, charIndex, matched, smB, capts: typed,
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
      let ntLit = newLit nt.int16
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
        if inClosure(`q`, `cSym`, `ntLit`, regex):
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
  q, cSym, cprev, c: int32
) {.inline.} =
  var captx: int
  var matched = true
  for n, capt in smA.items:
    genSubmatch(
      q, n, c, cSym, cPrev, capt, captx, i, matched, smB, capts, regex)
  swap(smA, smB)
  smB.setLen(0)

macro genEoeTable(
  matched: bool,
  q: int32,
  regex: static Regex
): untyped =
  ## Generate Eoe table
  result = newStmtList()
  var caseStmtQ: seq[NimNode]
  caseStmtQ.add(q)
  for i, t in regex.dfa.table.pairs:
    if symEoe in t:
      let trueLit = newLit true
      caseStmtQ.add(newTree(nnkOfBranch,
        newLit i.int32,
        quote do:
          `matched` = `trueLit`))
  doAssert caseStmtQ.len > 1
  let falseLit = newLit false
  caseStmtQ.add(newTree(nnkElse,
    quote do:
      `matched` = `falseLit`))
  result.add(
    newTree(nnkCaseStmt, caseStmtQ))
  when defined(reDumpMacro):
    echo "==== genEoeTable ===="
    echo repr(result)

macro genSymMatchTable(
  q, qnext, c, cSym: int32,
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
        let symLit = newLit symDigit
        symIfs.add(newTree(nnkElifBranch,
          quote do:
            isDecimal(Rune(`c`)),
          quote do:
            `qnext` = `tLit`
            `cSym` = `symLit`))
      of symWord:
        let tLit = newLit regex.dfa.table[i][symWord]
        let symLit = newLit symWord
        symIfs.add(newTree(nnkElifBranch,
          quote do:
            isWord(Rune(`c`)),
          quote do:
            `qnext` = `tLit`
            `cSym` = `symLit`))
      of symAny:
        let lineBreakLit = newLit lineBreakRune.int32
        let tLit = newLit regex.dfa.table[i][symAny]
        let symLit = newLit symAny
        symIfs.add(newTree(nnkElifBranch,
          quote do:
            `c` != `lineBreakLit`,
          quote do:
            `qnext` = `tLit`
            `cSym` = `symLit`))
      of symAnyNl:
        let tLit = newLit regex.dfa.table[i][symAnyNl]
        let symLit = newLit symAnyNl
        symIfs.add(newTree(nnkElifBranch,
          quote do:
            true,
          quote do:
            `qnext` = `tLit`
            `cSym` = `symLit`))
      else:
        doAssert false
        discard
    if symIfs.len > 0:
      let tLit = newLit -1'i32
      symIfs.add(newTree(nnkElse,
        quote do:
          `qnext` = `tLit`))
      qBranches.add(newTree(nnkOfBranch,
        newLit i.int32,
        newStmtList(
          newTree(nnkIfStmt, symIfs))))
  if qBranches.len > 0:
    let tLit = newLit -1'i32
    caseStmtQ.add(qBranches)
    caseStmtQ.add(newTree(nnkElse,
      quote do:
        `qnext` = `tLit`))
    result.add(newTree(nnkCaseStmt, caseStmtQ))
  when defined(reDumpMacro):
    echo "==== genSymMatchTable ===="
    echo repr(result)

macro genTable(
  q, qnext, c: int32,
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
      caseStmtC.add(newTree(nnkOfBranch,
        newLit c2,
        quote do:
          `qnext` = `t2Lit`))
    let qtLit = newLit -1'i32
    caseStmtC.add(newTree(nnkElse,
      quote do:
        `qnext` = `qtLit`))
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
    cSym: int32
    cPrev = -1'i32
    c: int32
    q = 0'i32
    qnext = 0'i32
    i = 0
  # workaround for https://github.com/nim-lang/Nim/issues/13252
  const hasTransionsZ = regex.transitions.z.len > 0
  const groupCount = regex.groupsCount
  smA.add((0'i16, -1))
  for r in text.runes:
    c = r.int32
    cSym = c
    genTable(q, qnext, c, regex)
    if (qnext == -1'i32).unlikely:
      # XXX when no ascii mode
      genSymMatchTable(q, qnext, c, cSym, regex)
      if (qnext == -1'i32).unlikely:
        return
    when hasTransionsZ:
      submatch(smA, smB, capts, regex, i, q, cSym, cPrev, c)
    q = qnext
    cPrev = r.int32
    inc i
  genEoeTable(result, q, regex)
  when hasTransionsZ:
    if not result:
      return
    submatch(smA, smB, capts, regex, i, q, symEoe, cPrev, symEoe)
    if smA.len == 0:
      result = false
      return
    constructSubmatches(captures, capts, smA[0][1], groupCount)
