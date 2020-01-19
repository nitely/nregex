import unicode
import algorithm
import strutils
import sets
import tables
import parseutils
import sequtils
import deques

import unicodedb/properties
import unicodedb/types
import unicodeplus except isUpper, isLower

type
  RegexError* = object of ValueError
  ## raised when the pattern
  ## is not a valid regex

proc `%%`(
  formatstr: string,
  a: openArray[string]
): string {.noSideEffect, raises: [].} =
  ## same as ``"$#" % ["foo"]`` but
  ## returns empty string on error
  try:
    formatstr % a
  except ValueError:
    ""

proc `%%`(formatstr: string, a: string): string =
  formatstr %% [a]

proc check(cond: bool, msg: string) =
  if not cond:
    raise newException(RegexError, msg)

proc isAsciiPrintable(s: string): bool =
  result = true
  for c in s.runes:
    case c.int
    of ' '.ord .. '~'.ord:
      discard
    else:
      return false

proc check(cond: bool, msg: string, at: int, exp: string) =
  if not cond:
    # todo: overflow checks
    const spaces = repeat(' ', "\n".len)
    var exp = exp.replace("\n", spaces)
    var start = max(0, at-15)
    var mark = at
    var expMsg = msg
    expMsg.add("\n")
    if not exp.runeSubStr(start, at-1).isAsciiPrintable:
      start = at-1
      let cleft = "~$# chars~" %% $start
      mark = cleft.len+1
      expMsg.add(cleft)
    elif start > 0:
      let cleft = "~$# chars~" %% $start
      mark = cleft.len+15
      expMsg.add(cleft)
    expMsg.add(exp.runeSubStr(start, 30))
    if start+30 < exp.len:
      expMsg.add("~$# chars~" %% $(exp.len - start - 30))
    expMsg.add("\n")
    expMsg.add(strutils.align("^", mark))
    raise newException(RegexError, expMsg)

template prettyCheck(cond: bool, msg: string) {.dirty.} =
  check(cond, msg, startPos, sc.raw)

const
  # This is used as start
  # and end of string. It should
  # be invalid code, but while it
  # works it simplifies things a bit.
  # An alternative would be opt[Rune]
  # or just using int32 and convert
  # Rune to int when needed
  invalidRune = Rune(-1)
  # `\n` is platform specific in
  # Nim and not the actual `\n`
  lineBreakRune = Rune(10)

proc toRune(s: string): Rune =
  result = s.runeAt(0)

type
  Flag = enum
    flagCaseInsensitive,  # i
    flagNotCaseInsensitive,  # -i
    flagMultiLine,  # m
    flagNotMultiLine,  # -m
    flagAnyMatchNewLine,  # s
    flagNotAnyMatchNewLine,  # -s
    flagUnGreedy,  # U
    flagNotUnGreedy,  # -U
    flagUnicode,  # u
    flagNotUnicode,  # -u
    flagVerbose,  # x
    flagNotVerbose  # -x
  NodeKind = enum
    reChar,
    reCharCI,
    reJoiner,  # ~
    reGroupStart,  # (
    reGroupEnd,  # )
    reOr,  # |
    reZeroOrMore,  # *
    reOneOrMore,  # +
    reZeroOrOne,  # ?
    reRepRange,  # {n,m}
    reStartSym,  # ^
    reEndSym,  # $
    reStartSymML,  # ^ multi-line
    reEndSymML,  # $ multi-line
    reStart,  # \A
    reEnd,  # \z
    reWordBoundary,  # \b
    reNotWordBoundary,  # \B
    reWord,  # \w
    reDigit,  # \d
    reWhiteSpace,  # \s
    reUCC,  # \pN or \p{Nn}
    reNotAlphaNum,  # \W
    reNotDigit,  # \D
    reNotWhiteSpace,  # \S
    reNotUCC,  # \PN or \P{Nn}
    reAny,  # .
    reAnyNL,  # . new-line
    reWordBoundaryAscii,  # \b ascii only
    reNotWordBoundaryAscii,  # \B ascii only
    reWordAscii,  # \w ascii only
    reDigitAscii,  # \d ascii only
    reWhiteSpaceAscii,  # \s ascii only
    reNotAlphaNumAscii,  # \W ascii only
    reNotDigitAscii,  # \D ascii only
    reNotWhiteSpaceAscii,  # \S ascii only
    reAnyAscii,  # . ascii only
    reAnyNLAscii,  # . new-line ascii only
    reInSet,  # [abc]
    reNotSet,  # [^abc]
    reLookahead,  # (?=...)
    reLookbehind,  # (?<=...)
    reNotLookahead,  # (?!...)
    reNotLookbehind,  # (?<!...)
    reSkip,  # dummy
    reEOE  # End of expression
  Node = object
    kind: NodeKind
    cp: Rune
    next: seq[int16]
    isGreedy: bool
    # reGroupStart, reGroupEnd
    idx: int16  # todo: rename?
    isCapturing: bool
    name: string
    flags: seq[Flag]
    # reRepRange
    min, max: int16
    # reInSet, reNotSet
    cps: HashSet[Rune]
    ranges: seq[Slice[Rune]]  # todo: interval tree
    shorthands: seq[Node]
    # reUCC, reNotUCC
    cc: UnicodeCategorySet

proc toCharNode(r: Rune): Node =
  ## return a ``Node`` that is meant to be matched
  ## against text characters
  Node(kind: reChar, cp: r)

proc initJoinerNode(): Node =
  ## return a ``Node`` of ``reJoiner`` kind.
  ## Joiners are temporary nodes,
  ## they serve to generate the NFA
  ## but they are never part of it
  Node(kind: reJoiner, cp: "~".toRune)

proc initEOENode(): Node =
  ## return the end-of-expression ``Node``.
  ## This is a dummy node that marks a match as successful
  Node(kind: reEOE, cp: "¿".toRune)

template initSetNodeImpl(result: var Node, k: NodeKind) =
  ## base node
  assert k in {reInSet, reNotSet}
  result = Node(
    kind: k,
    cp: "¿".toRune,
    cps: initHashSet[Rune](),
    ranges: @[],
    shorthands: @[])

proc initSetNode(): Node =
  ## return a set ``Node``,
  ## parsed from an expression such as ``[a-z]``
  initSetNodeImpl(result, reInSet)

proc initNotSetNode(): Node =
  ## return a negated set ``Node``,
  ## parsed from an expression such as ``[^a-z]``
  initSetNodeImpl(result, reNotSet)

proc initGroupStart(
  name: string = "",
  flags: seq[Flag] = @[],
  isCapturing = true
): Node =
  ## return a ``reGroupStart`` node
  Node(
    kind: reGroupStart,
    cp: "(".toRune,
    name: name,
    flags: flags,
    isCapturing: isCapturing)

proc isEmpty(n: Node): bool =
  ## check if a set ``Node`` is empty
  assert n.kind in {reInSet, reNotSet}
  result = (
    n.cps.len == 0 and
    n.ranges.len == 0 and
    n.shorthands.len == 0)

proc isWord(r: Rune): bool {.inline.} =
  utmWord in unicodeTypes(r)

proc isWordAscii(r: Rune): bool {.inline.} =
  ## return ``true`` if the given
  ## rune is in ``[A-Za-z0-9]`` range
  case r.int
  of 'A'.ord .. 'Z'.ord,
      'a'.ord .. 'z'.ord,
      '0'.ord .. '9'.ord,
      '_'.ord:
    true
  else:
    false

template isWordBoundaryImpl(r, nxt, alnumProc): bool =
  let
    isWord = r != invalidRune and alnumProc(r)
    isNxtWord = nxt != invalidRune and alnumProc(nxt)
  ((isWord and not isNxtWord) or
   (not isWord and isNxtWord))

proc isWordBoundary(r: Rune, nxt: Rune): bool {.inline.} =
  ## check if current match
  ## is a boundary (i.e the end of a word)
  isWordBoundaryImpl(r, nxt, isWord)

proc isWordBoundaryAscii(r: Rune, nxt: Rune): bool {.inline.} =
  ## check if current match
  ## is a boundary. Match ascii only
  isWordBoundaryImpl(r, nxt, isWordAscii)

proc match(n: Node, r: Rune, nxt: Rune): bool =
  ## match for ``Node`` of assertion kind.
  ## Return whether the node matches
  ## the current characters or not
  case n.kind
  of reStart, reStartSym:
    r == invalidRune
  of reEnd, reEndSym:
    nxt == invalidRune
  of reStartSymML:
    (r == invalidRune or
     r == lineBreakRune)
  of reEndSymML:
    (nxt == invalidRune or
     nxt == lineBreakRune)
  of reWordBoundary:
    isWordBoundary(r, nxt)
  of reNotWordBoundary:
    not isWordBoundary(r, nxt)
  of reWordBoundaryAscii:
    isWordBoundaryAscii(r, nxt)
  of reNotWordBoundaryAscii:
    not isWordBoundaryAscii(r, nxt)
  of reLookahead:
    n.cp == nxt
  of reNotLookahead:
    n.cp != nxt
  of reLookbehind:
    n.cp == r
  of reNotLookbehind:
    n.cp != r
  else:
    assert false
    false

proc `<=`(x, y: Rune): bool =
  x.int <= y.int

proc contains(sr: seq[Slice[Rune]], r: Rune): bool =
  result = false
  for sl in sr:
    result = r in sl
    if result:
      break

proc isWhiteSpace(r: Rune): bool {.inline.} =
  utmWhiteSpace in unicodeTypes(r)

proc isWhiteSpaceAscii(r: Rune): bool {.inline.} =
  case r.int
  of ' '.ord,
      '\t'.ord,
      '\L'.ord,
      '\r'.ord,
      '\f'.ord,
      '\v'.ord:
    true
  else:
    false

proc isDigitAscii(r: Rune): bool {.inline.} =
  case r.int
  of '0'.ord .. '9'.ord:
    true
  else:
    false

proc isAnyAscii(r: Rune): bool {.inline.} =
  (r.int <= int8.high and
   r != lineBreakRune)

# todo: can not use unicodeplus due to
# https://github.com/nim-lang/Nim/issues/7059
proc swapCase(r: Rune): Rune =
  # Note a character can be
  # non-lower and non-upper
  if r.isUpper():
    result = r.toLower()
  elif r.isLower():
    result = r.toUpper()
  else:
    result = r

proc match(n: Node, r: Rune): bool =
  ## match for ``Node`` of matchable kind.
  ## Return whether the node matches
  ## the current character or not
  assert r != invalidRune
  case n.kind
  of reEOE:
    false
  of reWord:
    r.isWord()
  of reNotAlphaNum:
    not r.isWord()
  of reDigit:
    r.isDecimal()
  of reNotDigit:
    not r.isDecimal()
  of reWhiteSpace:
    r.isWhiteSpace()
  of reNotWhiteSpace:
    not r.isWhiteSpace()
  of reInSet, reNotSet:
    var matches = (
      r in n.cps or
      r in n.ranges)
    if not matches:
      for nn in n.shorthands:
        matches = nn.match(r)
        if matches: break
    ((matches and n.kind == reInSet) or
     (not matches and n.kind == reNotSet))
  of reAny:
    r != lineBreakRune
  of reAnyNL:
    true
  of reCharCI:
    r == n.cp or r == n.cp.swapCase()
  of reWordAscii:
    r.isWordAscii()
  of reDigitAscii:
    r.isDigitAscii()
  of reWhiteSpaceAscii:
    r.isWhiteSpaceAscii()
  of reUCC:
    r.unicodeCategory() in n.cc
  of reNotAlphaNumAscii:
    not r.isWordAscii()
  of reNotDigitAscii:
    not r.isDigitAscii()
  of reNotWhiteSpaceAscii:
    not r.isWhiteSpaceAscii()
  of reNotUCC:
    r.unicodeCategory() notin n.cc
  of reAnyAscii:
    r.isAnyAscii()
  of reAnyNLAscii:
    r.isAnyAscii() or r == lineBreakRune
  else:
    assert n.kind == reChar
    n.cp == r

const
  opKind = {
    reJoiner,
    reOr,
    reZeroOrMore,
    reOneOrMore,
    reZeroOrOne,
    reRepRange}
  assertionKind = {
    reStartSym,
    reEndSym,
    reStartSymML,
    reEndSymML,
    reStart,
    reEnd,
    reWordBoundary,
    reNotWordBoundary,
    reWordBoundaryAscii,
    reNotWordBoundaryAscii,
    reLookahead,
    reLookbehind,
    reNotLookahead,
    reNotLookbehind}
  shorthandKind = {
    reWord,
    reDigit,
    reWhiteSpace,
    reUCC,
    reNotAlphaNum,
    reNotDigit,
    reNotWhiteSpace,
    reNotUCC,
    reWordAscii,
    reDigitAscii,
    reWhiteSpaceAscii,
    reNotAlphaNumAscii,
    reNotDigitAscii,
    reNotWhiteSpaceAscii}
  matchableKind = {
    reChar,
    reCharCI,
    reWord,
    reDigit,
    reWhiteSpace,
    reUCC,
    reNotAlphaNum,
    reNotDigit,
    reNotWhiteSpace,
    reNotUCC,
    reAny,
    reAnyNL,
    reInSet,
    reNotSet,
    reWordAscii,
    reDigitAscii,
    reWhiteSpaceAscii,
    reNotAlphaNumAscii,
    reNotDigitAscii,
    reNotWhiteSpaceAscii,
    reAnyAscii,
    reAnyNLAscii}
  repetitionKind = {
    reZeroOrMore,
    reOneOrMore,
    reRepRange}
  groupKind = {
    reGroupStart,
    reGroupEnd}
  matchTransitionKind = {
    reWhiteSpace,
    reUCC,
    reNotAlphaNum,
    reNotDigit,
    reNotWhiteSpace,
    reNotUCC,
    reInSet,
    reNotSet}

proc cmp(x, y: Rune): int =
  x.int - y.int

proc `$`(n: Node): string =
  ## return the string representation
  ## of a `Node`. The string is always
  ## equivalent to the original
  ## expression but not necessarily equal
  # Note this is not complete. Just
  # what needed for debugging so far
  case n.kind
  of reZeroOrMore,
      reOneOrMore,
      reZeroOrOne:
    if n.isGreedy:
      n.cp.toUTF8 & "?"
    else:
      n.cp.toUTF8
  of reRepRange:
    "¿"  # Invalid
  of reStart:
    "\\A"
  of reEnd:
    "\\z"
  of reWordBoundary:
    "\\b"
  of reNotWordBoundary:
    "\\B"
  of shorthandKind:
    '\\' & n.cp.toUTF8
  of reInSet, reNotSet:
    var str = ""
    str.add('[')
    if n.kind == reNotSet:
      str.add('^')
    var
      cps = newSeq[Rune](n.cps.len)
      i = 0
    for cp in n.cps:
      cps[i] = cp
      inc i
    for cp in cps.sorted(cmp):
      str.add(cp.toUTF8)
    for sl in n.ranges:
      str.add(sl.a.toUTF8 & '-' & sl.b.toUTF8)
    for nn in n.shorthands:
      str.add($nn)
    str.add(']')
    str
  of reSkip:
    "SKIP"
  of reEOE:
    "EOE"
  else:
    n.cp.toUTF8

#proc `$`(n: seq[Node]): string {.used.} =
#  result = newStringOfCap(n.len)
#  for nn in n:
#    result.add($nn)

type
  Scanner[T: Rune|Node] = ref object
    ## A scanner is a common
    ## construct for reading data
    raw: string
    s: seq[T]
    pos: int

proc newScanner[T](s: seq[T]): Scanner[T] =
  Scanner[T](s: s, pos: 0)

proc scan[T](s: seq[T]): Scanner[T] =
  newScanner(s)

proc scan(raw: string): Scanner[Rune] =
  Scanner[Rune](
    raw: raw,
    s: raw.toRunes,
    pos: 0)

iterator items[T](sc: Scanner[T]): T =
  ## the yielded item gets consumed
  while sc.pos <= sc.s.high:
    inc sc.pos
    yield sc.s[sc.pos - 1]

iterator mitems[T](sc: var Scanner[T]): var T =
  ## the yielded item gets consumed
  while sc.pos <= sc.s.high:
    inc sc.pos
    yield sc.s[sc.pos - 1]

proc finished[T](sc: Scanner[T]): bool =
  sc.pos > sc.s.high

proc prev[T](sc: Scanner[T]): T =
  sc.s[sc.pos - 1]

proc curr[T](sc: Scanner[T]): T =
  sc.s[sc.pos]

proc next[T](sc: Scanner[T]): T =
  ## return current item and consume it
  result = sc.s[sc.pos]
  inc sc.pos

proc peekImpl[T](sc: Scanner[T], default: T): T {.inline.} =
  ## same as ``curr`` except it
  ## returns a default/invalid value when
  ## the data is fully consumed
  if sc.pos > sc.s.high:
    default
  else:
    sc.s[sc.pos]

proc peek(sc: Scanner[Rune]): Rune =
  peekImpl(sc, invalidRune)

proc peek(sc: Scanner[Node]): Node =
  peekImpl(sc, initEOENode())

iterator peek[T](sc: Scanner[T]): (T, T) =
  for s in sc:
    yield (s, sc.peek)

proc find(sc: Scanner[Rune], r: Rune): int =
  ## return number of consumed chars.
  ## The scanner's position is not moved.
  ## ``-1`` is returned when char is not found
  result = 0
  let pos = sc.pos
  while true:
    if sc.finished:
      result = -1
      break
    if sc.curr == r:
      break
    discard sc.next()
    inc result
  sc.pos = pos

proc toShorthandNode(r: Rune): Node =
  ## the given character must be a shorthand or
  ## else a ``CharNode`` is returned
  case r
  of "w".toRune:
    Node(kind: reWord, cp: r)
  of "d".toRune:
    Node(kind: reDigit, cp: r)
  of "s".toRune:
    Node(kind: reWhiteSpace, cp: r)
  of "W".toRune:
    Node(kind: reNotAlphaNum, cp: r)
  of "D".toRune:
    Node(kind: reNotDigit, cp: r)
  of "S".toRune:
    Node(kind: reNotWhiteSpace, cp: r)
  else:
    r.toCharNode

proc toAssertionNode(r: Rune): Node =
  ## the given character must be an assertion or
  ## else a ``CharNode`` is returned
  case r
  of "A".toRune:
    Node(kind: reStart, cp: r)
  of "z".toRune:
    Node(kind: reEnd, cp: r)
  of "b".toRune:
    Node(kind: reWordBoundary, cp: r)
  of "B".toRune:
    Node(kind: reNotWordBoundary, cp: r)
  else:
    r.toCharNode

proc toEscapedSeqNode(r: Rune): Node =
  ## the given character must be an
  ## escaped sequence or else a regular char
  ## Node is returned
  case r
  of "a".toRune:
    Node(kind: reChar, cp: "\x07".toRune)
  of "f".toRune:
    Node(kind: reChar, cp: "\x0C".toRune)
  of "t".toRune:
    Node(kind: reChar, cp: "\t".toRune)
  of "n".toRune:
    Node(kind: reChar, cp: "\L".toRune)
  of "r".toRune:
    Node(kind: reChar, cp: "\r".toRune)
  of "v".toRune:
    Node(kind: reChar, cp: "\x0B".toRune)
  else:
    r.toCharNode

proc toEscapedNode(r: Rune): Node =
  ## return either a shorthand,
  ## an assertion, or a char node
  result = r.toShorthandNode
  if result.kind == reChar:
    result = r.toAssertionNode
  if result.kind == reChar:
    result = r.toEscapedSeqNode

proc parseUnicodeLit(sc: Scanner[Rune], size: int): Node =
  let startPos = sc.pos-1
  var rawCP = newString(size)
  for i in 0 ..< size:
    prettyCheck(
      not sc.finished,
      ("Invalid unicode literal. " &
       "Expected $# hex digits, but found $#") %% [$size, $i])
    prettyCheck(
      sc.curr.int in {
        '0'.ord .. '9'.ord,
        'a'.ord .. 'z'.ord,
        'A'.ord .. 'Z'.ord},
      ("Invalid unicode literal. " &
       "Expected hex digit, but found $#") %% $sc.curr)
    rawCP[i] = sc.next().int.char
  var cp = 0
  discard parseHex(rawCP, cp)
  prettyCheck(
    cp != -1 and cp <= int32.high,
    "Invalid unicode literal. $# value is too big" %% rawCP)
  result = Rune(cp).toCharNode

proc parseUnicodeLitX(sc: Scanner[Rune]): Node =
  let startPos = sc.pos-1
  assert sc.peek == "{".toRune
  discard sc.next()
  let litEnd = sc.find("}".toRune)
  prettyCheck(
    litEnd != -1,
    "Invalid unicode literal. Expected `}`")
  prettyCheck(
    litEnd <= 8,
    ("Invalid unicode literal. " &
     "Expected at most 8 chars, found $#") %% $litEnd)
  result = parseUnicodeLit(sc, litEnd)
  assert sc.peek == "}".toRune
  discard sc.next()

proc parseOctalLit(sc: Scanner[Rune]): Node =
  let startPos = sc.pos
  var rawCP = newString(3)
  for i in 0 ..< 3:
    prettyCheck(
      not sc.finished,
      ("Invalid octal literal. " &
       "Expected 3 octal digits, but found $#") %% $i)
    prettyCheck(
      sc.curr.int in {'0'.ord .. '7'.ord},
      ("Invalid octal literal. " &
       "Expected octal digit, but found $#") %% $sc.curr)
    rawCP[i] = sc.next().int.char
  var cp = 0
  discard parseOct(rawCP, cp)
  result = Rune(cp).toCharNode

proc parseCC(s: string): UnicodeCategorySet =
  try:
    result = s.categoryMap.UnicodeCategorySet
  except ValueError:
    try:
      result = s.categorySetMap
    except ValueError:
      check(false, "Invalid unicode name?")

proc parseUnicodeNameX(sc: Scanner[Rune]): Node =
  let startPos = sc.pos-1
  assert sc.peek == "{".toRune
  discard sc.next()
  let nameEnd = sc.find("}".toRune)
  prettyCheck(
    nameEnd != -1,
    "Invalid unicode name. Expected `}`")
  var name = newString(nameEnd)
  for i in 0 ..< nameEnd:
    prettyCheck(
      sc.curr.int in {
        'a'.ord .. 'z'.ord,
        'A'.ord .. 'Z'.ord},
      "Invalid unicode name. " &
      "Expected chars in {'a'..'z', 'A'..'Z'}")
    name[i] = sc.next().int.char
  assert sc.peek == "}".toRune
  discard sc.next()
  prettyCheck(
    name in [
      "Cn", "Lu", "Ll", "Lt", "Mn", "Mc", "Me", "Nd", "Nl",
      "No", "Zs", "Zl", "Zp", "Cc", "Cf", "Cs", "Co", "Cn",
      "Lm", "Lo", "Pc", "Pd", "Ps", "Pe", "Pi", "Pf", "Po",
      "Sm", "Sc", "Sk", "So", "C", "L", "M", "N",
      "Z", "P", "S"],
    "Invalid unicode name. Found $#" %% name)
  result = Node(
    kind: reUCC,
    cp: "¿".toRune,
    cc: name.parseCC)

proc parseUnicodeName(sc: Scanner[Rune]): Node =
  let startPos = sc.pos-1
  case sc.peek
  of "{".toRune:
    result = parseUnicodeNameX(sc)
  else:
    prettyCheck(
      sc.peek in [
        "C".toRune, "L".toRune, "M".toRune, "N".toRune,
        "Z".toRune, "P".toRune, "S".toRune],
      "Invalid unicode name. Found $#" %% sc.peek.toUTF8)
    result = Node(
      kind: reUCC,
      cp: "¿".toRune,
      cc: sc.next().toUTF8.parseCC)

proc parseEscapedSeq(sc: Scanner[Rune]): Node =
  ## Parse a escaped sequence
  case sc.curr
  of "u".toRune:
    discard sc.next()
    result = parseUnicodeLit(sc, 4)
  of "U".toRune:
    discard sc.next()
    result = parseUnicodeLit(sc, 8)
  of "x".toRune:
    discard sc.next()
    case sc.peek
    of "{".toRune:
      result = parseUnicodeLitX(sc)
    else:
      result = parseUnicodeLit(sc, 2)
  of "0".toRune .. "7".toRune:
    result = parseOctalLit(sc)
  of "p".toRune:
    discard sc.next()
    result = parseUnicodeName(sc)
  of "P".toRune:
    discard sc.next()
    result = parseUnicodeName(sc)
    result.kind = reNotUCC
  else:
    result = next(sc).toEscapedNode

proc parseSetEscapedSeq(sc: Scanner[Rune]): Node =
  ## Just like regular ``parseEscapedSeq``
  ## but treats assertions as chars (ignore escaping)
  let cp = sc.peek
  result = parseEscapedSeq(sc)
  if result.kind in assertionKind:
    result = cp.toCharNode

proc parseAsciiSet(sc: Scanner[Rune]): Node =
  ## Parse an ascii set (i.e: ``[:ascii:]``).
  ## The ascii set will get expanded
  ## and merged with the outer set
  let startPos = sc.pos
  assert sc.peek == ":".toRune
  discard sc.next()
  result = case sc.peek
  of "^".toRune:
    discard sc.next()
    initNotSetNode()
  else:
    initSetNode()
  var name = newStringOfCap(16)
  for r in sc:
    if r == ":".toRune:
      break
    name.add(r.toUTF8)
  prettyCheck(
    sc.peek == "]".toRune,
    "Invalid ascii set. Expected [:name:]")
  discard sc.next
  case name
  of "alpha":
    result.ranges.add([
      "a".toRune .. "z".toRune,
      "A".toRune .. "Z".toRune])
  of "alnum":
    result.ranges.add([
      "0".toRune .. "9".toRune,
      "a".toRune .. "z".toRune,
      "A".toRune .. "Z".toRune])
  of "ascii":
    result.ranges.add(
      "\x00".toRune .. "\x7F".toRune)
  of "blank":
    result.cps.incl(toHashSet([
      "\t".toRune, " ".toRune]))
  of "cntrl":
    result.ranges.add(
      "\x00".toRune .. "\x1F".toRune)
    result.cps.incl("\x7F".toRune)
  of "digit":
    result.ranges.add(
      "0".toRune .. "9".toRune)
  of "graph":
    result.ranges.add(
      "!".toRune .. "~".toRune)
  of "lower":
    result.ranges.add(
      "a".toRune .. "z".toRune)
  of "print":
    result.ranges.add(
      " ".toRune .. "~".toRune)
  of "punct":
    result.ranges.add([
      "!".toRune .. "/".toRune,
      ":".toRune .. "@".toRune,
      "[".toRune .. "`".toRune,
      "{".toRune .. "~".toRune])
  of "space":
    result.cps.incl(toHashSet([
      "\t".toRune, "\L".toRune, "\v".toRune,
      "\f".toRune, "\r".toRune, " ".toRune]))
  of "upper":
    result.ranges.add(
      "A".toRune .. "Z".toRune)
  of "word":
    result.ranges.add([
      "0".toRune .. "9".toRune,
      "a".toRune .. "z".toRune,
      "A".toRune .. "Z".toRune])
    result.cps.incl("_".toRune)
  of "xdigit":
    result.ranges.add([
      "0".toRune .. "9".toRune,
      "a".toRune .. "f".toRune,
      "A".toRune .. "F".toRune])
  else:
    prettyCheck(
      false,
      "Invalid ascii set. `$#` is not a valid name" %% name)

proc parseSet(sc: Scanner[Rune]): Node =
  ## parse a set atom (i.e ``[a-z]``) into a
  ## ``Node`` of ``reInSet`` or ``reNotSet`` kind.
  ## This proc is PCRE compatible and
  ## handles a ton of edge cases
  let startPos = sc.pos
  result = case sc.peek
  of "^".toRune:
    discard sc.next()
    initNotSetNode()
  else:
    initSetNode()
  var
    hasEnd = false
    cps = newSeq[Rune]()
  for cp in sc:
    case cp
    of "]".toRune:
      hasEnd = not result.isEmpty or cps.len > 0
      if hasEnd:
        break
      cps.add(cp)
    of "\\".toRune:
      let nn = parseSetEscapedSeq(sc)
      case nn.kind
      of reChar:
        cps.add(nn.cp)
      else:
        assert nn.kind in shorthandKind
        result.shorthands.add(nn)
        # can't be range so discard
        if sc.peek == "-".toRune:
          cps.add(sc.next())
    of "-".toRune:
      if sc.finished:
        # no end
        continue
      if cps.len == 0:
        cps.add(cp)
        continue
      var last: Rune
      case sc.peek
      of "]".toRune:
        cps.add(cp)
        continue
      of "\\".toRune:
        discard sc.next()
        let nn = parseSetEscapedSeq(sc)
        check(
          nn.kind == reChar,
          "Invalid set range. Range can't contain " &
          "a character-class or assertion",
          sc.pos-1,
          sc.raw)
        last = nn.cp
      else:
        assert(not sc.finished)
        last = sc.next()
      let first = cps.pop()
      check(
        first <= last,
        "Invalid set range. " &
        "Start must be lesser than end",
        sc.pos,
        sc.raw)
      result.ranges.add(first .. last)
      if sc.peek == "-".toRune:
        cps.add(sc.next())
    of "[".toRune:
      if sc.peek == ":".toRune:
        # todo: rename shorhands
        result.shorthands.add(parseAsciiSet(sc))
      else:
        cps.add(cp)
    else:
      cps.add(cp)
  # todo: use ref and set to nil when empty
  result.cps.incl(cps.toHashSet)
  prettyCheck(
    hasEnd,
    "Invalid set. Missing `]`")

proc parseRepRange(sc: Scanner[Rune]): Node =
  ## parse a repetition range ``{n,m}``
  let startPos = sc.pos
  var
    first, last: string
    hasFirst = false
    curr = ""
  for cp in sc:
    if cp == "}".toRune:
      last = curr
      break
    if cp == ",".toRune:
      first = curr
      curr = ""
      hasFirst = true
      continue
    prettyCheck(
      cp.int in '0'.ord .. '9'.ord,
      "Invalid repetition range. Range can only contain digits")
    curr.add(char(cp.int))
  if not hasFirst:  # {n}
    first = curr
  if first.len == 0:  # {,m} or {,}
    first.add('0')
  if last.len == 0:  # {n,} or {,}
    last = "-1"
  var
    firstNum: int
    lastNum: int
  when (NimMajor, NimMinor, NimPatch) < (0, 19, 9):
    type MyError = ref OverflowError
  else:
    type MyError = ref ValueError
  try:
    discard parseInt(first, firstNum)
    discard parseInt(last, lastNum)
  except MyError:
    prettyCheck(
      false,
      "Invalid repetition range. Max value is $#" %% $int16.high)
  prettyCheck(
    firstNum <= int16.high and
    lastNum <= int16.high,
    "Invalid repetition range. Max value is $#" %% $int16.high)
  # for perf reasons. This becomes a?a?a?...
  # too many parallel states
  prettyCheck(
    not (lastNum - firstNum > 100),
    ("Invalid repetition range. " &
     "Expected 100 repetitions or less, " &
     "but found: $#") %% $(lastNum - firstNum))
  result = Node(
    kind: reRepRange,
    min: firstNum.int16,
    max: lastNum.int16)

proc toFlag(r: Rune): Flag =
  result = case r
  of "i".toRune:
    flagCaseInsensitive
  of "m".toRune:
    flagMultiLine
  of "s".toRune:
    flagAnyMatchNewLine
  of "U".toRune:
    flagUnGreedy
  of "u".toRune:
    flagUnicode
  of "x".toRune:
    flagVerbose
  else:
    # todo: return err and show a better error msg
    raise newException(RegexError,
      ("Invalid group flag, found $# " &
       "but expected one of: i, m, s, U or u") %% $r)

proc toNegFlag(r: Rune): Flag =
  result = case r
  of "i".toRune:
    flagNotCaseInsensitive
  of "m".toRune:
    flagNotMultiLine
  of "s".toRune:
    flagNotAnyMatchNewLine
  of "U".toRune:
    flagNotUnGreedy
  of "u".toRune:
    flagNotUnicode
  of "x".toRune:
    flagNotVerbose
  else:
    # todo: return err and show a better error msg
    raise newException(RegexError,
      ("Invalid group flag, found -$# " &
       "but expected one of: -i, -m, -s, -U or -u") %% $r)

template checkEmptyGroup() {.dirty.} =
  prettyCheck(
    peek(sc) != toRune(")"),
    "Invalid group. Empty group is not allowed")

proc parseGroupTag(sc: Scanner[Rune]): Node =
  ## parse a special group (name, flags, non-captures).
  ## Return a regular ``reGroupStart``
  ## if it's not special enough
  # A regular group
  let startPos = sc.pos
  if sc.peek != "?".toRune:
    checkEmptyGroup()
    result = initGroupStart()
    return
  discard sc.next()  # Consume "?"
  case sc.peek
  of ":".toRune:
    discard sc.next()
    checkEmptyGroup()
    result = initGroupStart(isCapturing = false)
  of "P".toRune:
    discard sc.next()
    prettyCheck(
      sc.peek == "<".toRune,
      "Invalid group name. Missing `<`")
    discard sc.next()  # Consume "<"
    var name = newStringOfCap(75)
    for r in sc:
      if r == ">".toRune:
        break
      prettyCheck(
        r.int in {
          'a'.ord .. 'z'.ord,
          'A'.ord .. 'Z'.ord,
          '0'.ord .. '9'.ord,
          '-'.ord, '_'.ord},
        ("Invalid group name. Expected char in " &
         "{'a'..'z', 'A'..'Z', '0'..'9', '-', '_'}, " &
         "but found `$#`") %% $r)
      name.add(r.int.char)
    prettyCheck(
      name.len > 0,
      "Invalid group name. Name can't be empty")
    prettyCheck(
      sc.prev == ">".toRune,
      "Invalid group name. Missing `>`")
    checkEmptyGroup()
    result = initGroupStart(name)
  of "i".toRune,
      "m".toRune,
      "s".toRune,
      "U".toRune,
      "u".toRune,
      "x".toRune,
      "-".toRune:
    var
      flags: seq[Flag] = @[]
      isNegated = false
    for cp in sc:
      if cp == ":".toRune:
        checkEmptyGroup()
        break
      if cp == "-".toRune:
        isNegated = true
        continue
      if isNegated:
        flags.add(toNegFlag(cp))
      else:
        flags.add(toFlag(cp))
      if sc.peek == ")".toRune:
        break
    result = initGroupStart(
      flags = flags,
      isCapturing = false)
  #reLookahead,
  #reLookbehind,
  of "=".toRune:
    discard sc.next()
    # todo: support sets and more
    case sc.peek
    of "\\".toRune:
      let n = parseEscapedSeq(sc)
      prettyCheck(
        n.kind == reChar,
        "Invalid lookahead. A " &
        "character was expected, but " &
        "found a special symbol")
      result = Node(kind: reLookahead, cp: n.cp)
    else:
      prettyCheck(
        not sc.finished,
        "Invalid lookahead. A character " &
        "was expected, but found nothing (end of string)")
      result = Node(kind: reLookahead, cp: sc.next())
    prettyCheck(
      sc.peek == ")".toRune,
      "Invalid lookahead, expected closing symbol")
    discard sc.next()
  else:
    prettyCheck(
      false,
      "Invalid group. Unknown group type")

proc subParse(sc: Scanner[Rune]): Node =
  let r = sc.prev
  case r
  of "\\".toRune:
    sc.parseEscapedSeq()
  of "[".toRune:
    sc.parseSet()
  of "{".toRune:
    sc.parseRepRange()
  of "(".toRune:
    sc.parseGroupTag()
  of "|".toRune:
    Node(kind: reOr, cp: r)
  of "*".toRune:
    Node(kind: reZeroOrMore, cp: r)
  of "+".toRune:
    Node(kind: reOneOrMore, cp: r)
  of "?".toRune:
    Node(kind: reZeroOrOne, cp: r)
  of ")".toRune:
    Node(kind: reGroupEnd, cp: r)
  of "^".toRune:
    Node(kind: reStartSym, cp: r)
  of "$".toRune:
    Node(kind: reEndSym, cp: r)
  of ".".toRune:
    Node(kind: reAny, cp: r)
  else:
    r.toCharNode

proc skipWhiteSpace(sc: Scanner[Rune], vb: seq[bool]): bool =
  ## skip white-spaces and comments on verbose mode
  result = false
  if vb.len == 0 or not vb[vb.len-1]:
    return
  result = case sc.prev
  of " ".toRune,
      "\t".toRune,
      "\L".toRune,
      "\r".toRune,
      "\f".toRune,
      "\v".toRune:
    true
  of "#".toRune:
    for r in sc:
      if r == "\L".toRune:
        break
    true
  else:
    false

proc verbosity(
  vb: var seq[bool],
  sc: Scanner[Rune],
  n: Node
) =
  ## update verbose mode on current group
  case n.kind:
  of reGroupStart:
    if vb.len > 0:
      vb.add(vb[vb.high])
    else:
      vb.add(false)
    for f in n.flags:
      case f:
      of flagVerbose:
        vb[vb.high] = true
      of flagNotVerbose:
        vb[vb.high] = false
      else:
        discard
    if sc.peek == ")".toRune:  # (?flags)
      if vb.len > 1:  # set outter group
        vb[vb.high - 1] = vb[vb.high]
      else:
        vb.add(vb[vb.high])
  of reGroupEnd:
    if vb.len > 0:
      discard vb.pop()
    # else: unbalanced parentheses,
    # it'll raise later
  else:
    discard

proc parse(expression: string): seq[Node] =
  ## convert a ``string`` regex expression
  ## into a ``Node`` expression
  result = newSeqOfCap[Node](expression.len)
  var vb = newSeq[bool]()
  let sc = expression.scan()
  for _ in sc:
    if sc.skipWhiteSpace(vb): continue
    result.add(sc.subParse())
    vb.verbosity(sc, result[^1])

proc greediness(expression: seq[Node]): seq[Node] =
  ## apply greediness to an expression
  result = newSeqOfCap[Node](expression.len)
  var sc = expression.scan()
  for n in sc.mitems():
    if (n.kind in repetitionKind or
        n.kind == reZeroOrOne) and
        sc.peek.kind == reZeroOrOne:
      n.isGreedy = true
      discard sc.next
    result.add(n)

type
  GroupsCapture = tuple
    count: int16
    names: OrderedTable[string, int16]

proc fillGroups(expression: var seq[Node]): GroupsCapture =
  ## populate group indices, names and capturing mark
  var
    groups = newSeq[int]()
    names = initOrderedTable[string, int16]()
    count = 0'i16
  for i, n in expression.mpairs:
    case n.kind
    of reGroupStart:
      groups.add(i)
      if n.isCapturing:
        n.idx = count
        inc count
      if n.name.len > 0:
        assert n.isCapturing
        names[n.name] = n.idx
    of reGroupEnd:
      check(
        groups.len > 0,
        "Invalid capturing group. " &
        "Found too many closing symbols")
      let start = groups.pop()
      n.isCapturing = expression[start].isCapturing
      n.idx = expression[start].idx
    else:
      discard
    check(
      count < int16.high,
      ("Invalid number of capturing groups, " &
       "the limit is $#") %% $(int16.high - 1))
  check(
    groups.len == 0,
    "Invalid capturing group. " &
    "Found too many opening symbols")
  result = (
    count: count,
    names: names)

proc toAsciiKind(k: NodeKind): NodeKind =
  case k
  of reWordBoundary:
    reWordBoundaryAscii
  of reNotWordBoundary:
    reNotWordBoundaryAscii
  of reWord:
    reWordAscii
  of reDigit:
    reDigitAscii
  of reWhiteSpace:
    reWhiteSpaceAscii
  of reNotAlphaNum:
    reNotAlphaNumAscii
  of reNotDigit:
    reNotDigitAscii
  of reNotWhiteSpace:
    reNotWhiteSpaceAscii
  of reAny:
    reAnyAscii
  of reAnyNL:
    reAnyNLAscii
  else:
    k

proc toggle(f: Flag): Flag =
  ## toggle regular flag to
  ## negated flag and the other way around
  case f
  of flagCaseInsensitive:
    flagNotCaseInsensitive
  of flagNotCaseInsensitive:
    flagCaseInsensitive
  of flagMultiLine:
    flagNotMultiLine
  of flagNotMultiLine:
    flagMultiLine
  of flagAnyMatchNewLine:
    flagNotAnyMatchNewLine
  of flagNotAnyMatchNewLine:
    flagAnyMatchNewLine
  of flagUnGreedy:
    flagNotUnGreedy
  of flagNotUnGreedy:
    flagUnGreedy
  of flagUnicode:
    flagNotUnicode
  of flagNotUnicode:
    flagUnicode
  of flagVerbose:
    flagNotVerbose
  of flagNotVerbose:
    flagVerbose

proc squash(flags: seq[seq[Flag]]): array[Flag, bool] =
  ## Nested groups may contain flags,
  ## this will set/unset those flags
  ## in order. It should be done each time
  ## there is a group start/end
  for ff in flags:
    for f in ff:
      result[f.toggle()] = false
      result[f] = true

proc applyFlag(n: var Node, f: Flag) =
  case f
  of flagAnyMatchNewLine:
    if n.kind == reAny:
      n.kind = reAnyNL
  of flagMultiLine:
    case n.kind
    of reStartSym:
      n.kind = reStartSymML
    of reEndSym:
      n.kind = reEndSymML
    else:
      discard
  of flagCaseInsensitive:
    if n.kind == reChar and n.cp != n.cp.swapCase():
      n.kind = reCharCI
    # todo: apply recursevely to
    #       shorthands of reInSet/reNotSet (i.e: [:ascii:])
    if n.kind in {reInSet, reNotSet}:
      var cps = initHashSet[Rune]()
      cps.incl(n.cps)
      for cp in cps:
        let cpsc = cp.swapCase()
        if cp != cpsc:
          n.cps.incl(cpsc)
      for sl in n.ranges[0 .. ^1]:
        let
          cpa = sl.a.swapCase()
          cpb = sl.b.swapCase()
        if sl.a != cpa and sl.b != cpb:
          n.ranges.add(cpa .. cpb)
  of flagUnGreedy:
    if n.kind in opKind:
      n.isGreedy = not n.isGreedy
  of flagNotUnicode:
    n.kind = n.kind.toAsciiKind()
    if n.kind in {reInSet, reNotSet}:
      for nn in n.shorthands.mitems:
        nn.kind = nn.kind.toAsciiKind()
  else:
    assert f in {
      flagNotAnyMatchNewLine,
      flagNotMultiLine,
      flagNotCaseInsensitive,
      flagNotUnGreedy,
      flagUnicode,
      flagVerbose,
      flagNotVerbose}

proc applyFlags(expression: seq[Node]): seq[Node] =
  ## apply flags to each group
  result = newSeqOfCap[Node](expression.len)
  var flags = newSeq[seq[Flag]]()
  var sc = expression.scan()
  for n in sc.mitems():
    # (?flags)
    # Orphan flags are added to current group
    case n.kind
    of reGroupStart:
      if n.flags.len == 0:
        flags.add(@[])
        result.add(n)
        continue
      if sc.peek.kind == reGroupEnd:  # (?flags)
        discard sc.next()
        if flags.len > 0:
          flags[flags.len - 1].add(n.flags)
        else:
          flags.add(n.flags)
        continue  # skip (
      flags.add(n.flags)
    of reGroupEnd:
      discard flags.pop()
    else:
      let ff = flags.squash()
      for f in Flag.low .. Flag.high:
        if ff[f]:
          applyFlag(n, f)
    result.add(n)

proc expandOneRepRange(subExpr: seq[Node], n: Node): seq[Node] =
  ## expand a repetition-range expression
  ## into the equivalent repeated expression
  assert n.kind == reRepRange
  if n.max == -1:  # a{n,} -> aaa*
    result = newSeqOfCap[Node](subExpr.len * (n.min + 1) + 1)
    for _ in 0 ..< n.min:
      result.add(subExpr)
    result.add(Node(
      kind: reZeroOrMore,
      cp: "*".toRune,
      isGreedy: n.isGreedy))
  elif n.min == n.max:  # a{n} -> aaa
    result = newSeqOfCap[Node](subExpr.len * n.max)
    for _ in 0 ..< n.max - 1:
      result.add(subExpr)
  else:  # a{n,m} -> aaa?a?
    assert n.min < n.max
    result = newSeqOfCap[Node](subExpr.len * n.max + n.max - n.min)
    for _ in 0 ..< n.min:
      result.add(subExpr)
    for _ in n.min ..< n.max - 1:
      result.add(Node(
        kind: reZeroOrOne,
        cp: "?".toRune,
        isGreedy: n.isGreedy))
      result.add(subExpr)
    result.add(Node(
      kind: reZeroOrOne,
      cp: "?".toRune,
      isGreedy: n.isGreedy))

proc expandRepRange(expression: seq[Node]): seq[Node] =
  ## expand every repetition range
  result = newSeqOfCap[Node](expression.len)
  var i: int
  for n in expression:
    if n.kind != reRepRange:
      result.add(n)
      continue
    check(
      result.len > 0,
      "Invalid repeition range, " &
      "nothing to repeat")
    let lastNode = result[^1]
    case lastNode.kind
    of reGroupEnd:
      i = 0
      for ne in result.reversed:
        inc i
        if ne.kind == reGroupStart and ne.idx == lastNode.idx:
          break
      assert result[result.len-i].kind == reGroupStart
      result.add(result[result.len-i .. result.len-1].expandOneRepRange(n))
    of matchableKind:
      result.add(result[result.len-1 .. result.len-1].expandOneRepRange(n))
    else:
      raise newException(RegexError, (
        "Invalid repetition range, either " &
        "char, shorthand (i.e: \\w), group, or set " &
        "expected before repetition range"))

proc joinAtoms(expression: seq[Node]): seq[Node] =
  ## Put a ``~`` joiner between atoms. An atom is
  ## a piece of expression that would loose
  ## meaning when breaking it up (i.e.: ``a~(b|c)*~d``)
  result = newSeqOfCap[Node](expression.len * 2)
  var atomsCount = 0
  for n in expression:
    case n.kind
    of matchableKind, assertionKind:
      inc atomsCount
      if atomsCount > 1:
        atomsCount = 1
        result.add(initJoinerNode())
    of reGroupStart:
      if atomsCount > 0:
        result.add(initJoinerNode())
      atomsCount = 0
    of reOr:
      atomsCount = 0
    of reGroupEnd,
        reZeroOrMore,
        reOneOrMore,
        reZeroOrOne,
        reRepRange:
      inc atomsCount
    else:
      assert false
    result.add(n)

type
  Associativity = enum
    ## Operator associativity. Unary ops are
    ## right[-to-left] and binary ops are
    ## left[-to-right]
    asyRight
    asyLeft
  OpsPA = tuple
    precedence: int
    associativity: Associativity

proc opsPA(nk: NodeKind): OpsPA =
  ## return the precedence and
  ## associativity of a given node kind
  assert nk in opKind
  case nk
  of reRepRange,
      reZeroOrMore,
      reOneOrMore,
      reZeroOrOne:
    result = (5, asyRight)
  of reJoiner:
    result = (4, asyLeft)
  of reOr:
    result = (3, asyLeft)
  else:
    assert false

proc hasPrecedence(a: NodeKind, b: NodeKind): bool =
  ## Check ``b`` has precedence over ``a``.
  ## Both ``a`` and ``b`` are expected to
  ## be valid operators. Unary operators such
  ## as: ``*``, ``?`` and ``+`` have right-to-left
  ## associativity. Binary operators
  ## such as: ``|`` (or) and ``~`` (joiner) have
  ## left-to-right associativity
  result =
    (opsPA(b).associativity == asyRight and
      opsPA(b).precedence <= opsPA(a).precedence) or
    (opsPA(b).associativity == asyLeft and
      opsPA(b).precedence < opsPA(a).precedence)

proc popGreaterThan(ops: var seq[Node], op: Node): seq[Node] =
  assert op.kind in opKind
  result = newSeqOfCap[Node](ops.len)
  while (ops.len > 0 and
      ops[ops.len - 1].kind in opKind and
      ops[ops.len - 1].kind.hasPrecedence(op.kind)):
    result.add(ops.pop())

proc popUntilGroupStart(ops: var seq[Node]): seq[Node] =
  result = newSeqOfCap[Node](ops.len)
  while true:
    let op = ops.pop()
    result.add(op)
    if op.kind == reGroupStart:
      break

proc rpn(expression: seq[Node]): seq[Node] =
  ## An adaptation of the Shunting-yard algorithm
  ## for producing `Reverse Polish Notation` out of
  ## an expression specified in infix notation.
  ## It supports regex primitives including groups.
  ## The point of doing this is greatly simplifying
  ## the parsing of the regular expression into an NFA.
  ## Suffix notation removes nesting and so it can
  ## be parsed in a linear way instead of recursively
  result = newSeqOfCap[Node](expression.len)
  var ops = newSeq[Node]()
  for n in expression:
    case n.kind
    of matchableKind, assertionKind:
      result.add(n)
    of reGroupStart:
      ops.add(n)
    of reGroupEnd:
      result.add(ops.popUntilGroupStart())
      result.add(n)
    of opKind:
      result.add(ops.popGreaterThan(n))
      ops.add(n)
    else:
      assert false
  # reverse ops
  for i in 1 .. ops.len:
    result.add(ops[ops.len - i])

type
  End = seq[int16]
    ## store all the last
    ## states of a given state.
    ## Avoids having to recurse
    ## a state to find its ends,
    ## but have to keep them up-to-date

proc combine(
    nfa: var seq[Node],
    ends: var seq[End],
    org: int16,
    target: int16) =
  ## combine ends of ``org``
  ## with ``target``
  for e in ends[org]:
    for i, ni in nfa[e].next.mpairs:
      if nfa[ni].kind == reEOE:
        ni = target
  ends[org] = ends[target]

proc update(
    ends: var seq[End],
    ni: int16,
    next: openArray[int16]) =
  ## update the ends of Node ``ni``
  ## to point to ends of ``n.outA``
  ## and ``n.outB``. If either outA
  ## or outB are ``0`` (EOE),
  ## the ends will point to itself
  ends[ni].setLen(0)
  for n in next:
    if n == 0:
        ends[ni].add(ni)
    else:
        ends[ni].add(ends[n])

proc nfa(expression: var seq[Node]): seq[Node] =
  ## Thompson's construction
  result = newSeqOfCap[Node](expression.len + 2)
  result.add(initEOENode())
  const eoe = 0'i16
  var
    ends = newSeq[End](expression.len + 1)
    states = newSeq[int16]()
  if expression.len == 0:
    states.add(eoe)
  for n in expression.mitems():
    assert n.next.len == 0
    check(
      result.high < int16.high,
      ("The expression is too long, " &
       "limit is ~$#") %% $int16.high)
    let ni = result.len.int16
    case n.kind
    of matchableKind, assertionKind:
      n.next.add(eoe)
      ends.update(ni, [eoe])
      result.add(n)
      states.add(ni)
    of reJoiner:
      let
        stateB = states.pop()
        stateA = states.pop()
      result.combine(ends, stateA, stateB)
      states.add(stateA)
    of reOr:
      check(
        states.len >= 2,
        "Invalid OR conditional, nothing to " &
        "match at right/left side of the condition")
      let
        stateB = states.pop()
        stateA = states.pop()
      n.next.add([stateA, stateB])
      ends.update(ni, n.next)
      result.add(n)
      states.add(ni)
    of reZeroOrMore:
      check(
        states.len >= 1,
        "Invalid `*` operator, " &
        "nothing to repeat")
      let stateA = states.pop()
      n.next.add([stateA, eoe])
      ends.update(ni, n.next)
      result.combine(ends, stateA, ni)
      result.add(n)
      states.add(ni)
      if n.isGreedy:
        swap(result[^1].next[0], result[^1].next[1])
    of reOneOrMore:
      check(
        states.len >= 1,
        "Invalid `+` operator, " &
        "nothing to repeat")
      let stateA = states.pop()
      n.next.add([stateA, eoe])
      ends.update(ni, n.next)
      result.combine(ends, stateA, ni)
      result.add(n)
      states.add(stateA)
      if n.isGreedy:
        swap(result[^1].next[0], result[^1].next[1])
    of reZeroOrOne:
      check(
        states.len >= 1,
        "Invalid `?` operator, " &
        "nothing to make optional")
      let stateA = states.pop()
      n.next.add([stateA, eoe])
      ends.update(ni, n.next)
      result.add(n)
      states.add(ni)
      if n.isGreedy:
        swap(result[^1].next[0], result[^1].next[1])
    of reGroupStart:
      let stateA = states.pop()
      n.next.add(stateA)
      ends.update(ni, n.next)
      result.add(n)
      states.add(ni)
    of reGroupEnd:
      n.next.add(eoe)
      ends.update(ni, n.next)
      let stateA = states.pop()
      result.combine(ends, stateA, ni)
      result.add(n)
      states.add(stateA)
    else:
      assert(false, "Unhandled node: $#" %% $n.kind)
  assert states.len == 1
  result.add(Node(
    kind: reSkip,
    cp: "¿".toRune,
    next: states))

type
  Zclosure = seq[int16]
  TeClosure = seq[(int16, Zclosure)]

proc teClosure(
  result: var TeClosure,
  nfa: seq[Node],
  state: int16,
  visited: var set[int16],
  zTransitions: Zclosure
) =
  if state in visited:
    return
  visited.incl(state)
  var zTransitionsCurr = zTransitions
  if nfa[state].kind in groupKind + assertionKind:
    zTransitionsCurr.add(state)
  if nfa[state].kind in {reInSet, reNotSet}:  # XXX don't do this in ascii mode
    # XXX skip if subset of {reAny, reAnyNl, reDigit, reWord} for reInSet
    if nfa[state].shorthands.len > 0:
      zTransitionsCurr.add(state)
    result.add((state, zTransitionsCurr))
    return
  if nfa[state].kind in matchTransitionKind:  # XXX don't do this in ascii mode
    zTransitionsCurr.add(state)
    result.add((state, zTransitionsCurr))
    return
  if nfa[state].kind in matchableKind + {reEOE}:
    result.add((state, zTransitionsCurr))
    return
  for s in nfa[state].next:
    teClosure(result, nfa, s, visited, zTransitionsCurr)

proc teClosure(
  result: var TeClosure,
  nfa: seq[Node],
  state: int16
) =
  var visited: set[int16]
  var zclosure: Zclosure
  for s in nfa[state].next:
    teClosure(result, nfa, s, visited, zclosure)

type
  Transitions = object
    all: seq[seq[int16]]
    allZ: seq[seq[int16]]
    z: seq[seq[Node]]

proc eRemoval(eNfa: var seq[Node]): Transitions =
  ## Remove e-transitions and return
  ## remaining state transtions and
  ## submatches, and zero matches.
  ## Transitions are added in matching order (BFS),
  ## which may help matching performance
  #echo eNfa
  result.all.setLen(eNfa.len)
  result.allZ.setLen(eNfa.len)
  var statesMap = newSeq[int16](eNfa.len)
  for i in 0 .. statesMap.len-1:
    statesMap[i] = -1
  var statePos = 0'i16
  let start = int16(eNfa.len-1)
  statesMap[start] = statePos
  inc statePos
  var closure: TeClosure
  var zc: seq[Node]
  var qw = initDeque[int16]()
  qw.addFirst(start)
  var qu: set[int16]
  qu.incl(start)
  while qw.len > 0:
    let qa = qw.popLast()
    closure.setLen(0)
    teClosure(closure, eNfa, qa)
    eNfa[qa].next.setLen(0)  # XXX don't mutate this as we can grab next from result.all later
    for qb, zclosure in closure.items:
      eNfa[qa].next.add(qb)
      if statesMap[qb] == -1:
        statesMap[qb] = statePos
        inc statePos
      assert statesMap[qa] > -1
      assert statesMap[qb] > -1
      result.all[statesMap[qa]].add(statesMap[qb])
      result.allZ[statesMap[qa]].add(-1'i16)
      zc.setLen(0)
      for z in zclosure:
        zc.add(eNfa[z])
      if zc.len > 0:
        result.z.add(zc)
        result.allZ[statesMap[qa]][^1] = int16(result.z.len-1)
      if qb notin qu:
        qu.incl(qb)
        qw.addFirst(qb)
  result.all.setLen(statePos)
  result.allZ.setLen(statePos)
  var nfa = newSeq[Node](statePos)
  for en, nn in statesMap.pairs:
    if nn == -1:
      continue
    nfa[nn] = case eNfa[en].kind
      of matchTransitionKind:
        Node(kind: reAnyNl, cp: "#".toRune)
      else:
        eNfa[en]
    nfa[nn].next.setLen(0)
    for en2 in eNfa[en].next:
      assert statesMap[en2] > -1
      nfa[nn].next.add(statesMap[en2])
  eNfa.setLen(0)
  eNfa.add(nfa)

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
    of reCharCi:
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

proc dfa(nfa: seq[Node]): Dfa =
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
        result.table.add(default(DfaRow))
        result.closures.add(default(DfaClosure))
      result.table[qu[qa]][sym] = qu[t]
      result.cs.add(s)
      result.closures[qu[qa]][sym] = int32(result.cs.len-1)

type
  CaptNode = object
    parent: int
    bound: int
    idx: int
  Capts = seq[CaptNode]
  Captures = seq[seq[Slice[int]]]

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
    dfa: Dfa
    transitions: Transitions
    groupsCount: int16
    namedGroups: OrderedTable[string, int16]

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

proc match(
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
    regex.dfa.cs[regex.dfa.closures[q][symEoe]], i, cprev, -1'i32)
  if smA.len == 0:
    result[0] = false
    return
  result[1] = constructSubmatches(capts, smA[0][1], regex.groupsCount)

proc re*(s: string): Regex =
  var ns = s.parse
  let gc = ns.fillGroups()
  var names: OrderedTable[string, int16]
  if gc.names.len > 0:
    names = gc.names
  var exp = ns.greediness.applyFlags.expandRepRange.joinAtoms.rpn
  var nfa = exp.nfa
  let transitions = eRemoval(nfa)
  let dfa = dfa(nfa)
  result = Regex(
    dfa: dfa,
    transitions: transitions,
    groupsCount: gc.count,
    namedGroups: names)

proc matchCapt(s: string, exp: Regex): (bool, Captures) {.inline.} =
  return match(s, exp)

proc match2*(s: string, exp: Regex): bool {.inline.} =
  let (matched, _) = matchCapt(s, exp)
  return matched

when isMainModule:
  doAssert match2("abc", re"abc")
  doAssert match2("ab", re"a(b|c)")
  doAssert match2("ac", re"a(b|c)")
  doAssert not match2("ad", re"a(b|c)")
  doAssert match2("ab", re"(ab)*")
  doAssert match2("abab", re"(ab)*")
  doAssert not match2("ababc", re"(ab)*")
  doAssert not match2("a", re"(ab)*")
  doAssert match2("ab", re"(ab)+")
  doAssert match2("abab", re"(ab)+")
  doAssert not match2("ababc", re"(ab)+")
  doAssert not match2("a", re"(ab)+")
  doAssert match2("aa", re"\b\b\baa\b\b\b")
  doAssert not match2("cac", re"c\ba\bc")
  doAssert match2("abc", re"[abc]+")
  doAssert match2("abc", re"[\w]+")
  doAssert match2("弢弢弢", re"[\w]+")
  doAssert not match2("abc", re"[\d]+")
  doAssert match2("123", re"[\d]+")
  doAssert match2("abc$%&", re".+")
  doAssert not match2("abc$%&\L", re"(.+)")
  doAssert not match2("abc$%&\L", re".+")
  doAssert not match2("弢", re"\W")
  doAssert match2("$%&", re"\W+")
  doAssert match2("abc123", re"[^\W]+")

  doAssert matchCapt("aabcd", re"(aa)bcd") ==
    (true, @[@[0 .. 1]])
  doAssert matchCapt("aabc", re"(aa)(bc)") ==
    (true, @[@[0 .. 1], @[2 .. 3]])
  doAssert matchCapt("ab", re"a(b|c)") ==
    (true, @[@[1 .. 1]])
  doAssert matchCapt("ab", re"(ab)*") ==
    (true, @[@[0 .. 1]])
  doAssert matchCapt("abab", re"(ab)*") ==
    (true, @[@[0 .. 1, 2 .. 3]])
  doAssert matchCapt("ab", re"((a))b") ==
    (true, @[@[0 .. 0], @[0 .. 0]])
  doAssert matchCapt("c", re"((ab)*)c") ==
    (true, @[@[0 .. -1], @[]])
  doAssert matchCapt("aab", re"((a)*b)") ==
    (true, @[@[0 .. 2], @[0 .. 0, 1 .. 1]])
  doAssert matchCapt("abbbbcccc", re"a(b|c)*") ==
    (true, @[@[1 .. 1, 2 .. 2, 3 .. 3, 4 .. 4, 5 .. 5, 6 .. 6, 7 .. 7, 8 .. 8]])
  doAssert matchCapt("ab", re"(a*)(b*)") ==
    (true, @[@[0 .. 0], @[1 .. 1]])
  doAssert matchCapt("ab", re"(a)*(b)*") ==
    (true, @[@[0 .. 0], @[1 .. 1]])
  doAssert matchCapt("ab", re"(a)*b*") ==
    (true, @[@[0 .. 0]])
  doAssert matchCapt("abbb", re"((a(b)*)*(b)*)") ==
    (true, @[@[0 .. 3], @[0 .. 3], @[1 .. 1, 2 .. 2, 3 .. 3], @[]])
  doAssert matchCapt("aa", re"(a)+") ==
    (true, @[@[0 .. 0, 1 .. 1]])
  doAssert matchCapt("abab", re"(ab)+") ==
    (true, @[@[0 .. 1, 2 .. 3]])
  doAssert matchCapt("a", re"(a)?") ==
    (true, @[@[0 .. 0]])
  doAssert matchCapt("ab", re"(ab)?") ==
    (true, @[@[0 .. 1]])
  doAssert matchCapt("aaabbbaaa", re"(a*|b*)*") ==
    (true, @[@[0 .. 2, 3 .. 5, 6 .. 8]])
  doAssert matchCapt("abab", re"(a(b))*") ==
    (true, @[@[0 .. 1, 2 .. 3], @[1 .. 1, 3 .. 3]])
  doAssert matchCapt("aaanasdnasd", re"((a)*n?(asd)*)*") ==
    (true, @[@[0 .. 6, 7 .. 10], @[0 .. 0, 1 .. 1, 2 .. 2], @[4 .. 6, 8 .. 10]])
  doAssert matchCapt("aaanasdnasd", re"((a)*n?(asd))*") ==
    (true, @[@[0 .. 6, 7 .. 10], @[0 .. 0, 1 .. 1, 2 .. 2], @[4 .. 6, 8 .. 10]])
  doAssert matchCapt("abd", re"((ab)c)|((ab)d)") ==
    (true, @[@[], @[], @[0 .. 2], @[0 .. 1]])
  doAssert matchCapt("aaa", re"(a*)") ==
    (true, @[@[0 .. 2]])
  doAssert matchCapt("aaaa", re"(a*)(a*)") ==
    (true, @[@[0 .. 3], @[4 .. 3]])
  doAssert matchCapt("aaaa", re"(a*?)(a*?)") ==
    (true, @[@[0 .. -1], @[0 .. 3]])
  doAssert matchCapt("aaaa", re"(a)*(a)") ==
    (true, @[@[0 .. 0, 1 .. 1, 2 .. 2], @[3 .. 3]])
  



  doAssert match2("a", re"a")
  doAssert match2("a", re"\w")
