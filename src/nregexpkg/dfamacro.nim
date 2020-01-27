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
  q, c: int32,
  nt: int16,
  cs: static seq[Closure],
  closures: static seq[DfaClosure]
): untyped =
  #[
  case q:  # curr state
  of 1.int32:
    case c:  # curr char
    of 'A'.int32:
      case nt:  # next state
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
    if t.len == 0:  # end state
      continue
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
    if t.len == 0:  # end state
      continue
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
    doAssert branchBodyN.len > 0
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
  # workaround for https://github.com/nim-lang/Nim/issues/13252
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
    when regex2.transitions.z.len > 0:
      submatch(smA, smB, capts, regex, i, q, cPrev, c)
    q = qnext
    cPrev = r.int32
    inc i
  result[0] = symEoe in regex2.dfa.table[q]
  when regex2.transitions.z.len > 0:
    if not result[0]:
      return
    submatch(smA, smB, capts, regex, i, q, cPrev, symEoe)
    if smA.len == 0:
      result[0] = false
      return
    result[1] = constructSubmatches(capts, smA[0][1], regex2.groupsCount)
