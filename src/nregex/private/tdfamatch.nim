## Runtime matcher: interprets the TDFA tables,
## see ``tdfa``

import std/unicode
import std/algorithm
import std/tables

import common
import nodematch
import tdfa
import types

func nextRune(text: string, i: var int, isAscii: bool): Rune {.inline.} =
  if isAscii or text[i].ord <= 127:
    result = Rune(text[i])
    inc i
  else:
    fastRuneAt(text, i, result, true)

func transition(
  tdfa: Tdfa,
  q: int32,
  c: Rune,
  isAscii: bool
): int32 {.inline.} =
  ## transition index of state ``q`` on ``c``, or -1
  if c.int32 < 128:
    return tdfa.asciiTrans[q*128 + c.int32]
  template syms: untyped = tdfa.nonAsciiSyms[q]
  let si = syms.lowerBound(c.int32,
    func (x: tuple[sym, trans: int32], k: int32): int = cmp(x.sym, k))
  if si < syms.len and syms[si].sym == c.int32:
    return syms[si].trans
  if isAscii or tdfa.nonAsciiAlphabet.binarySearch(c.int32) != -1:
    return -1
  # runes not in the alphabet
  template st: untyped = tdfa.states[q]
  var bits = 0
  for pi, pred in st.preds.pairs:
    var matched = true
    for n in pred:
      if not match(n, c):
        matched = false
        break
    if matched:
      bits = bits or (1 shl pi)
  return st.predTrans[bits]

func initState(tdfa: Tdfa, text: string, start: int): int32 {.inline.} =
  if start > 0 and tdfa.ctxTests != {}:
    tdfa.initStates[ctxOf(tdfa.ctxTests, bwRuneAt(text, start-1))]
  else:
    0'i32

type
  Registers = object
    ## registers of every NFA state in the current
    ## TDFA state, plus a buffer to apply transitions
    a, b: seq[int]
    nTags: int

func initRegisters(tdfa: Tdfa): Registers =
  result.nTags = tdfa.nTags
  result.a = newSeq[int](max(1, tdfa.maxRegs*tdfa.nTags))
  result.b = newSeq[int](result.a.len)
  for r in result.a.mitems:
    r = -1

func setRegs(
  dst: var seq[int], di: int,
  src: seq[int], op: TdfaOp,
  tdfa: Tdfa, nTags, pos: int,
  copy: bool
) {.inline.} =
  ## registers of NFA state ``di`` are the
  ## registers of ``op.src`` plus the op tags.
  ## The source registers are copied if ``copy``,
  ## otherwise ``dst`` already holds them
  if op.src == fresh:
    for t in 0 .. nTags-1:
      dst[di*nTags + t] = -1
  elif copy:
    for t in 0 .. nTags-1:
      dst[di*nTags + t] = src[op.src*nTags + t]
  if op.tags != -1:
    for t in tdfa.tags[op.tags]:
      dst[di*nTags + t] = pos

func apply(regs: var Registers, tdfa: Tdfa, tr: TdfaTrans, pos: int) =
  let nTags = regs.nTags
  if nTags == 0:
    return
  var inPlace = true
  for i, op in tr.ops.pairs:
    if op.src != i and op.src != fresh:
      inPlace = false
      break
  if inPlace:
    for i, op in tr.ops.pairs:
      if op.src == fresh or op.tags != -1:
        setRegs(regs.a, i, regs.a, op, tdfa, nTags, pos, copy = false)
  else:
    for i, op in tr.ops.pairs:
      setRegs(regs.b, i, regs.a, op, tdfa, nTags, pos, copy = true)
    swap(regs.a, regs.b)

func acceptRegs(
  regs: Registers, tdfa: Tdfa, op: TdfaOp, pos: int
): seq[int] =
  result = newSeq[int](regs.nTags)
  if regs.nTags > 0:
    setRegs(result, 0, regs.a, op, tdfa, regs.nTags, pos, copy = true)

func setCaptures(m: var RegexMatch, regex: Regex, regs: seq[int]) =
  m.captures.setLen regex.groupsCount
  for g in 0 .. regex.groupsCount.int-1:
    let a = regs[g*2]
    let b = regs[g*2+1]
    m.captures[g] = if b == -1: nonCapture else: a .. b-1
  if regex.namedGroups.len > 0:
    m.namedGroups = regex.namedGroups

func matchImpl*(
  text: string,
  regex: Regex,
  m: var RegexMatch,
  noCaptures: bool,
  start = 0
): bool =
  ## Match the whole ``text`` from ``start``
  m.clear()
  template fsm: untyped = regex.tdfa
  let isAscii = reAscii in regex.flags
  var regs = if noCaptures: Registers() else: initRegisters(fsm)
  var q = initState(fsm, text, start)
  var i = start
  while i < text.len:
    let pos = i
    let c = nextRune(text, i, isAscii)
    let ti = transition(fsm, q, c, isAscii)
    if ti == -1:
      return false
    if not noCaptures:
      regs.apply(fsm, fsm.trans[ti], pos)
    q = fsm.trans[ti].target
  let ti = fsm.states[q].eoe
  if ti == -1:
    return false
  if not noCaptures:
    m.setCaptures(regex, acceptRegs(regs, fsm, fsm.trans[ti].accept, i))
  m.boundaries = start .. i-1
  return true

func findImpl*(
  text: string,
  regex: Regex,
  m: var RegexMatch,
  noCaptures: bool,
  start = 0
): bool =
  ## Find the leftmost-first match from ``start``.
  ## If ``noCaptures``, return the first match found;
  ## the match boundaries are not set then
  m.clear()
  template fsm: untyped = regex.tdfaFind
  let isAscii = reAscii in regex.flags
  var regs = if noCaptures: Registers() else: initRegisters(fsm)
  var best: seq[int]
  var matchEnd = -1
  var q = initState(fsm, text, start)
  var i = start
  while true:
    let pos = i
    let ti = if i < text.len:
      let c = nextRune(text, i, isAscii)
      transition(fsm, q, c, isAscii)
    else:
      fsm.states[q].eoe
    if ti == -1:
      break
    template tr: untyped = fsm.trans[ti]
    if tr.accept.src != noAccept:
      if noCaptures:
        return true
      best = acceptRegs(regs, fsm, tr.accept, pos)
      matchEnd = pos
    if tr.target == -1 or pos >= text.len:
      break
    if not noCaptures:
      regs.apply(fsm, tr, pos)
    q = tr.target
  if matchEnd == -1:
    return false
  m.setCaptures(regex, best)
  m.boundaries = best[fsm.nTags-1] .. matchEnd-1
  return true
