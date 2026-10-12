##[
A library for parsing, compiling, and executing
regular expressions. The match time is linear
in the length of the input. So, it can handle
input from untrusted users. The syntax is similar to PCRE
but lacks a few features that can not be implemented
while keeping the space/time complexity guarantees,
i.e.: backreferences and look-around assertions.

Syntax
******

Matching one character
######################

.. code-block::
  .          any character except new line (includes new line with s flag)
  \d         digit (\p{Nd})
  \D         not digit
  \pN        One-letter name Unicode character class
  \p{Greek}  Unicode character class (general category or script)
  \PN        Negated one-letter name Unicode character class
  \P{Greek}  negated Unicode character class (general category or script)

Character classes
#################

.. code-block::
  [xyz]         A character class matching either x, y or z (union).
  [^xyz]        A character class matching any character except x, y and z.
  [a-z]         A character class matching any character in range a-z.
  [[:alpha:]]   ASCII character class ([A-Za-z])
  [[:^alpha:]]  Negated ASCII character class ([^A-Za-z])
  [\[\]]        Escaping in character classes (matching [ or ])

Composites
##########

.. code-block::
  xy   concatenation (x followed by y)
  x|y  alternation (x or y, prefer x)

Repetitions
###########

.. code-block::
  x*       zero or more of x (greedy)
  x+       one or more of x (greedy)
  x?       zero or one of x (greedy)
  x*?      zero or more of x (ungreedy/lazy)
  x+?      one or more of x (ungreedy/lazy)
  x??      zero or one of x (ungreedy/lazy)
  x{n,m}   at least n x and at most m x (greedy)
  x{n,}    at least n x (greedy)
  x{n}     exactly n x
  x{n,m}?  at least n x and at most m x (ungreedy/lazy)
  x{n,}?   at least n x (ungreedy/lazy)
  x{n}?    exactly n x

Empty matches
#############

.. code-block::
  ^   the beginning of text (or start-of-line with multi-line mode)
  $   the end of text (or end-of-line with multi-line mode)
  \A  only the beginning of text (even with multi-line mode enabled)
  \z  only the end of text (even with multi-line mode enabled)
  \b  a Unicode word boundary (\w on one side and \W, \A, or \z on other)
  \B  not a Unicode word boundary

Grouping and flags
##################

.. code-block::
  (exp)          numbered capture group (indexed by opening parenthesis)
  (?P<name>exp)  named (also numbered) capture group (allowed chars: [_0-9a-zA-Z])
  (?:exp)        non-capturing group
  (?flags)       set flags within current group
  (?flags:exp)   set flags for exp (non-capturing)

Flags are each a single character. For example,
(?x) sets the flag x and (?-x) clears the flag x.
Multiple flags can be set or cleared at the same
time: (?xy) sets both the x and y flags, (?x-y)
sets the x flag and clears the y flag, and (?-xy)
clears both the x and y flags.

.. code-block::
  i  case-insensitive: letters match both upper and lower case
  m  multi-line mode: ^ and $ match begin/end of line
  s  allow . to match \L (new line)
  U  swap the meaning of x* and x*? (un-greedy mode)
  u  Unicode support (enabled by default)
  x  ignore whitespace and allow line comments (starting with `#`)

`All flags are disabled by default unless stated otherwise`

Escape sequences
################

.. code-block::
  \*         literal *, works for any punctuation character: \.+*?()|[]{}^$
  \a         bell (\x07)
  \f         form feed (\x0C)
  \t         horizontal tab
  \n         new line (\L)
  \r         carriage return
  \v         vertical tab (\x0B)
  \123       octal character code (up to three digits)
  \x7F       hex character code (exactly two digits)
  \x{10FFFF} any hex character code corresponding to a Unicode code point
  \u007F     hex character code (exactly four digits)
  \U0010FFFF hex character code (exactly eight digits)

Perl character classes (Unicode friendly)
#########################################

These classes are based on the definitions provided in
`UTS#18 <http://www.unicode.org/reports/tr18/#Compatibility_Properties>`_

.. code-block::
  \d  digit (\p{Nd})
  \D  not digit
  \s  whitespace (\p{White_Space})
  \S  not whitespace
  \w  word character (\p{Alphabetic} + \p{M} + \d + \p{Pc} + \p{Join_Control})
  \W  not word character

ASCII character classes
#######################

.. code-block::
  [[:alnum:]]   alphanumeric ([0-9A-Za-z])
  [[:alpha:]]   alphabetic ([A-Za-z])
  [[:ascii:]]   ASCII ([\x00-\x7F])
  [[:blank:]]   blank ([\t ])
  [[:cntrl:]]   control ([\x00-\x1F\x7F])
  [[:digit:]]   digits ([0-9])
  [[:graph:]]   graphical ([!-~])
  [[:lower:]]   lower case ([a-z])
  [[:print:]]   printable ([ -~])
  [[:punct:]]   punctuation ([!-/:-@\[-`{-~])
  [[:space:]]   whitespace ([\t\n\v\f\r ])
  [[:upper:]]   upper case ([A-Z])
  [[:word:]]    word characters ([0-9A-Za-z_])
  [[:xdigit:]]  hex digit ([0-9A-Fa-f])

]##

import std/tables
import std/sequtils
import std/unicode

import nregex/private/[
  common,
  parser,
  exptransformation,
  nfa,
  tdfa,
  types,
  tdfamatch,
  tdfamacro
]

export
  Regex,
  RegexMatch,
  RegexFlag,
  RegexError

const reNonCapture* = nonCapture
  ## capture of a group that did not match

template reImpl(s, flags: untyped): Regex =
  var groups: GroupsCapture
  var transitions: Transitions
  let nfaNodes = s
    .parse
    .transformExp(groups)
    .nfa(transitions)
  Regex(
    tdfa: tdfa(nfaNodes, transitions, groups.count, tmMatch),
    tdfaFind: tdfa(nfaNodes, transitions, groups.count, tmFind),
    groupsCount: groups.count,
    namedGroups: groups.names,
    flags: flags)

func re*(
  s: string,
  flags: set[RegexFlag] = {}
): Regex {.inline.} =
  reImpl(s, flags)

when not defined(forceRegexAtRuntime):
  func re*(
    s: static string,
    flags: static set[RegexFlag] = {}
  ): static Regex {.inline.} =
    reImpl(s, flags)

func group*(m: RegexMatch, i: int): Slice[int] {.inline.} =
  ## return the last capture of a given group,
  ## same as PCRE. It's ``reNonCapture`` if the
  ## group did not match. Captures of start > end
  ## are empty matches (i.e.: ``re"(\d?)"``)
  runnableExamples:
    var m: RegexMatch
    doAssert "abc".match(re"(\w)+", m)
    doAssert m.group(0) == 2 .. 2
    doAssert "abc".match(re"(\w)+|(d)", m)
    doAssert m.group(1) == reNonCapture

  m.captures[i]

func group*(m: RegexMatch, s: string): Slice[int] {.inline.} =
  ## return the last capture of a given named group
  runnableExamples:
    var m: RegexMatch
    doAssert "abc".match(re"(?P<foo>\w)+", m)
    doAssert m.group("foo") == 2 .. 2

  m.group(m.namedGroups[s])

func group*(m: RegexMatch, i: int, text: string): string =
  ## return the text of the last capture of a given
  ## group, or an empty string if the group did not match
  runnableExamples:
    let text = "hello beautiful world"
    var m: RegexMatch
    doAssert text.match(re"(hello) (?:([^\s]+)\s?)+", m)
    doAssert m.group(0, text) == "hello"
    doAssert m.group(1, text) == "world"

  if m.captures[i] == nonCapture: "" else: text[m.captures[i]]

func group*(m: RegexMatch, groupName: string, text: string): string =
  ## return the text of the last capture of a given named
  ## group, or an empty string if the group did not match
  runnableExamples:
    let text = "hello beautiful world"
    var m: RegexMatch
    doAssert text.match(re"(?P<greet>hello) (?:(?P<who>[^\s]+)\s?)+", m)
    doAssert m.group("greet", text) == "hello"
    doAssert m.group("who", text) == "world"

  m.group(m.namedGroups[groupName], text)

func groupsCount*(m: RegexMatch): int =
  ## return the number of capturing groups
  runnableExamples:
    var m: RegexMatch
    doAssert "ab".match(re"(a)(b)", m)
    doAssert m.groupsCount == 2

  m.captures.len

func groupNames*(m: RegexMatch): seq[string] =
  ## return the names of capturing groups.
  runnableExamples:
    let text = "hello world"
    var m: RegexMatch
    doAssert text.match(re"(?P<greet>hello) (?P<who>world)", m)
    doAssert m.groupNames() == @["greet", "who"]

  result = toSeq(m.namedGroups.keys)

func isInitialized*(re: Regex): bool {.inline.} =
  ## Check whether the regex has been initialized
  runnableExamples:
    var re: Regex
    doAssert not re.isInitialized
    re = re"foo"
    doAssert re.isInitialized

  re.tdfa.states.len > 0

when not defined(forceRegexAtRuntime):
  func match*(
    s: string,
    pattern: static Regex,
    m: var RegexMatch,
    start = 0
  ): bool {.inline.} =
    ## return a match if the whole string
    ## matches the regular expression. This
    ## is similar to ``find(text, re"^regex$", m)``,
    ## but has better performance
    runnableExamples:
      var m: RegexMatch
      doAssert "abcd".match(re"abcd", m)
      doAssert not "abcd".match(re"abc", m)

    const f: MatchFlags = {}
    result = tdfamacro.matchImpl(s, pattern, m, f, start)

  func match*(s: string, pattern: static Regex): bool {.inline.} =
    runnableExamples:
      doAssert "abcd".match(re"abcd")
      doAssert not "abcd".match(re"abc")

    var m: RegexMatch
    result = tdfamacro.matchImpl(s, pattern, m, {mfNoCaptures})

func match*(
  s: string,
  pattern: Regex,
  m: var RegexMatch,
  start = 0
): bool =
  ## return a match if the whole string
  ## matches the regular expression
  result = tdfamatch.matchImpl(s, pattern, m, false, start)

func match*(s: string, pattern: Regex): bool =
  var m: RegexMatch
  result = tdfamatch.matchImpl(s, pattern, m, true)

func contains*(s: string, pattern: Regex): bool =
  ## search for the pattern anywhere
  ## in the string. It returns as soon
  ## as there is a match, even when the
  ## expression has repetitions
  runnableExamples:
    doAssert re"bc" in "abcd"
    doAssert re"(23)+" in "23232"
    doAssert re"^(23)+$" notin "23232"

  var m: RegexMatch
  result = findImpl(s, pattern, m, true)

func find*(
  s: string,
  pattern: Regex,
  m: var RegexMatch,
  start = 0
): bool =
  ## search for the leftmost-first match from
  ## ``start``, same as PCRE
  runnableExamples:
    var m: RegexMatch
    doAssert "abcd".find(re"bc", m)
    doAssert m.boundaries == 1 .. 2
    doAssert "abcd".find(re"(a|ab)", m)
    doAssert m.boundaries == 0 .. 0

  result = findImpl(s, pattern, m, false, start)

iterator findAll*(
  s: string,
  pattern: Regex,
  start = 0
): RegexMatch =
  ## Find all non-overlapping matches.
  ## After an empty match, the search
  ## continues at the next char
  runnableExamples:
    var bounds: seq[Slice[int]]
    for m in findAll("aaa", re"a*"):
      bounds.add m.boundaries
    doAssert bounds == @[0 .. 2, 3 .. 2]

  var i = start
  var c: Rune
  var m: RegexMatch
  while i <= len(s):
    if not find(s, pattern, m, i):
      break
    yield m
    if m.boundaries.b+1 > m.boundaries.a:
      i = m.boundaries.b+1
    elif m.boundaries.a < len(s):  # empty match
      i = m.boundaries.a
      fastRuneAt(s, i, c, true)
    else:
      break

func findAll*(
  s: string,
  pattern: Regex,
  start = 0
): seq[RegexMatch] =
  for m in findAll(s, pattern, start):
    result.add m

when isMainModule:
  var m: RegexMatch

  doAssert match("abc", re(r"abc", {reAscii}), m)
  doAssert match("abc", re"abc", m)
  doAssert match("ab", re"a(b|c)", m)
  doAssert match("ac", re"a(b|c)", m)
  doAssert not match("ad", re"a(b|c)", m)
  doAssert match("ab", re"(ab)*", m)
  doAssert match("abab", re"(ab)*", m)
  doAssert not match("ababc", re"(ab)*", m)
  doAssert not match("a", re"(ab)*", m)
  doAssert match("ab", re"(ab)+", m)
  doAssert match("abab", re"(ab)+", m)
  doAssert not match("ababc", re"(ab)+", m)
  doAssert not match("a", re"(ab)+", m)
  doAssert match("aa", re"\b\b\baa\b\b\b", m)
  doAssert not match("cac", re"c\ba\bc", m)
  doAssert match("abc", re"[abc]+", m)
  doAssert match("abc", re"[\w]+", m)
  doAssert match("弢弢弢", re"[\w]+", m)
  doAssert not match("abc", re"[\d]+", m)
  doAssert match("123", re"[\d]+", m)
  doAssert match("abc$%&", re".+", m)
  doAssert not match("abc$%&\L", re"(.+)", m)
  doAssert not match("abc$%&\L", re".+", m)
  doAssert not match("弢", re"\W", m)
  doAssert match("$%&", re"\W+", m)
  doAssert match("abc123", re"[^\W]+", m)

  doAssert match("aabcd", re"(aa)bcd", m) and
    m.captures == @[0 .. 1]
  doAssert match("aabc", re"(aa)(bc)", m) and
    m.captures == @[0 .. 1, 2 .. 3]
  doAssert match("ab", re"a(b|c)", m) and
    m.captures == @[1 .. 1]
  doAssert match("ab", re"(ab)*", m) and
    m.captures == @[0 .. 1]
  doAssert match("abab", re"(ab)*", m) and
    m.captures == @[2 .. 3]
  doAssert match("ab", re"((a))b", m) and
    m.captures == @[0 .. 0, 0 .. 0]
  doAssert match("c", re"((ab)*)c", m) and
    m.captures == @[0 .. -1, nonCapture]
  doAssert match("aab", re"((a)*b)", m) and
    m.captures == @[0 .. 2, 1 .. 1]
  doAssert match("abbbbcccc", re"a(b|c)*", m) and
    m.captures == @[8 .. 8]
  doAssert match("ab", re"(a*)(b*)", m) and
    m.captures == @[0 .. 0, 1 .. 1]
  doAssert match("ab", re"(a)*(b)*", m) and
    m.captures == @[0 .. 0, 1 .. 1]
  doAssert match("ab", re"(a)*b*", m) and
    m.captures == @[0 .. 0]
  doAssert match("abbb", re"((a(b)*)*(b)*)", m) and
    m.captures == @[0 .. 3, 0 .. 3, 3 .. 3, nonCapture]
  doAssert match("aa", re"(a)+", m) and
    m.captures == @[1 .. 1]
  doAssert match("abab", re"(ab)+", m) and
    m.captures == @[2 .. 3]
  doAssert match("a", re"(a)?", m) and
    m.captures == @[0 .. 0]
  doAssert match("ab", re"(ab)?", m) and
    m.captures == @[0 .. 1]
  doAssert match("aaabbbaaa", re"(a*|b*)*", m) and
    m.captures == @[9 .. 8]
  doAssert match("abab", re"(a(b))*", m) and
    m.captures == @[2 .. 3, 3 .. 3]
  doAssert match("aaanasdnasd", re"((a)*n?(asd)*)*", m) and
    m.captures == @[11 .. 10, 2 .. 2, 8 .. 10]
  doAssert match("aaanasdnasd", re"((a)*n?(asd))*", m) and
    m.captures == @[7 .. 10, 2 .. 2, 8 .. 10]
  doAssert match("abd", re"((ab)c)|((ab)d)", m) and
    m.captures == @[nonCapture, nonCapture, 0 .. 2, 0 .. 1]
  doAssert match("aaa", re"(a*)", m) and
    m.captures == @[0 .. 2]
  doAssert match("aaaa", re"(a*)(a*)", m) and
    m.captures == @[0 .. 3, 4 .. 3]
  doAssert match("aaaa", re"(a*?)(a*?)", m) and
    m.captures == @[0 .. -1, 0 .. 3]
  doAssert match("aaaa", re"(a)*(a)", m) and
    m.captures == @[2 .. 2, 3 .. 3]
  
  doAssert match("abc", re"abc")
  doAssert not match("abc", re"abd")
  doAssert not match("abc", re"ab")
  doAssert not match("abc", re"b")
  doAssert not match("abc", re"c")

  doAssert re"bc" in "abcd"
  doAssert re"(23)+" in "23232"
  doAssert re"^(23)+$" notin "23232"
  doAssert re"\w" in "弢"
  doAssert re(r"\w", {reAscii}) notin "弢"
  doAssert re(r"\w", {reAscii}) in "a"

  doAssert "abcd".find(re"bc", m)
  doAssert not "abcd".find(re"de", m)
  doAssert "%ab%".find(re(r"\w{2}", {reAscii}), m)
  doAssert "%弢弢%".find(re"\w{2}", m)
  doAssert not "%弢弢%".find(re(r"\w{2}", {reAscii}), m)
  doAssert(
    "2222".find(re"(22)*", m) and
    m.group(0) == 2 .. 3)
  doAssert(
    "11222211".find(re"(22)+", m) and
    m.group(0) == 4 .. 5)
  
  doAssert match("650-253-0001", re"[0-9]+-[0-9]+-[0-9]+", m)
  doAssert not match("abc-253-0001", re"[0-9]+-[0-9]+-[0-9]+", m)
  doAssert not match("650-253", re"[0-9]+-[0-9]+-[0-9]+", m)
  doAssert not match("650-253-0001-abc", re"[0-9]+-[0-9]+-[0-9]+", m)
  doAssert match("650-253-0001", re"[0-9]+..*", m)
  doAssert not match("abc-253-0001", re"[0-9]+..*", m)
  doAssert not match("6", re"[0-9]+..*", m)

  doAssert match("abcabcabc", re"(?:(?:abc)){3}")
  doAssert match("abcabcabc", re"((abc)){3}")

  block:
    const re1 = re"(11)*+(111)*"
    doAssert match("", re1)
    doAssert match("11", re1)
    doAssert match("111", re1)
    doAssert match("11111", re1)
    doAssert match("1111111", re1)
    doAssert match("1111111111", re1)
    doAssert not match("1", re1)
  block:
    const re1 = re"(11)+(111)*"
    doAssert not match("", re1)
    doAssert match("11", re1)
    doAssert not match("111", re1)
    doAssert match("11111", re1)
  block:
    const re1 = re"(aabb)(ab)*"
    doAssert match("aabb", re1)
    doAssert match("aabbab", re1)
    doAssert match("aabbabab", re1)
    doAssert not match("ab", re1)
    doAssert not match("aabbaba", re1)
  block:
    const re1 = re"0(10)*"
    doAssert match("0", re1)
    doAssert match("010", re1)
    doAssert not match("", re1)
    doAssert not match("0101", re1)
    doAssert not match("0100", re1)
    doAssert not match("00", re1)
    doAssert not match("000", re1)
  block:
    const re1 = re"(11)*|(111)*"
    doAssert match("", re1)
    doAssert match("11", re1)
    doAssert match("111", re1)
    doAssert match("1111", re1)
    doAssert match("111111", re1)
    doAssert not match("1", re1)

  func findAllBounds(s: string, reg: Regex): seq[Slice[int]] =
    result = map(
      findAll(s, reg),
      func (m: RegexMatch): Slice[int] =
        m.boundaries)

  doAssert findAllBounds("abcabc", re"bc") == @[1 .. 2, 4 .. 5]
  doAssert findAllBounds("aΪⒶ弢aΪⒶ弢", re"Ⓐ") == @[3 .. 5, 13 .. 15]
