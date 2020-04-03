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
  dfa,
  dfamatch,
  dfamacro
]

export
  Regex,
  RegexMatch,
  RegexFlag,
  RegexError

template reImpl(s, flags: untyped): Regex =
  var groups: GroupsCapture
  var transitions: Transitions
  var alphabet: seq[AlphabetSym]
  let dfa = s
    .parse
    .transformExp(groups)
    .nfa(transitions)
    .dfa(alphabet)
    .minimize(alphabet)
  Regex(
    dfa: dfa,
    transitions: transitions,
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

iterator group*(m: RegexMatch, i: int): Slice[int] =
  ## return slices for a given group.
  ## Slices of start > end are empty
  ## matches (i.e.: ``re"(\d?)"``)
  ## and they are included same as in PCRE.
  runnableExamples:
    let text = "abc"
    var m: RegexMatch
    doAssert text.match(re"(\w)+", m)
    var captures = newSeq[string]()
    for bounds in m.group(0):
      captures.add(text[bounds])
    doAssert captures == @["a", "b", "c"]

  for capt in m.captures[i]:
    yield capt

func group*(m: RegexMatch, i: int): seq[Slice[int]] =
  ## return slices for a given group.
  ## Use the iterator version if you care about performance
  m.captures[i]

iterator group*(m: RegexMatch, s: string): Slice[int] =
  ## return slices for a given named group
  runnableExamples:
    let text = "abc"
    var m: RegexMatch
    doAssert text.match(re"(?P<foo>\w)+", m)
    var captures = newSeq[string]()
    for bounds in m.group("foo"):
      captures.add(text[bounds])
    doAssert captures == @["a", "b", "c"]

  for bounds in m.group(m.namedGroups[s]):
    yield bounds

func group*(m: RegexMatch, s: string): seq[Slice[int]] =
  ## return slices for a given named group.
  ## Use the iterator version if you care about performance
  m.group(m.namedGroups[s])

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

func group*(
  m: RegexMatch,
  groupName: string,
  text: string
): seq[string] = 
  ## return seq of captured text by group `groupName`
  runnableExamples:
    let text = "hello beautiful world"
    var m: RegexMatch
    doAssert text.match(re"(?P<greet>hello) (?:(?P<who>[^\s]+)\s?)+", m)
    doAssert m.group("greet", text) == @["hello"]
    doAssert m.group("who", text) == @["beautiful", "world"]

  result = newSeq[string]()
  for bounds in m.group(groupName):
    result.add text[bounds]

func groupFirstCapture*(
  m: RegexMatch,
  groupName: string,
  text: string
): string =
  ##  Return fist capture for a given capturing group
  runnableExamples:
    let text = "hello beautiful world"
    var m: RegexMatch
    doAssert text.match(re"(?P<greet>hello) (?:(?P<who>[^\s]+)\s?)+", m)
    doAssert m.groupFirstCapture("greet", text) == "hello"
    doAssert m.groupFirstCapture("who", text) == "beautiful"

  let captures = m.group(groupName, text)
  if captures.len > 0:
    return captures[0]
  else:
    return "" 

func groupLastCapture*(
  m: RegexMatch,
  groupName: string,
  text: string
): string =
  ##  Return last capture for a given capturing group
  runnableExamples:
    let text = "hello beautiful world"
    var m: RegexMatch
    doAssert text.match(re"(?P<greet>hello) (?:(?P<who>[^\s]+)\s?)+", m)
    doAssert m.groupLastCapture("greet", text) == "hello"
    doAssert m.groupLastCapture("who", text) == "world"

  let captures = m.group(groupName, text)
  if captures.len > 0:
    return captures[captures.len-1]
  else:
    return "" 

func isInitialized*(re: Regex): bool {.inline.} =
  ## Check whether the regex has been initialized
  runnableExamples:
    var re: Regex
    doAssert not re.isInitialized
    re = re"foo"
    doAssert re.isInitialized

  re.dfa.table.len > 0

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
    result = matchImpl(s, pattern, m, f, start)

  func match*(s: string, pattern: static Regex): bool {.inline.} =
    runnableExamples:
      doAssert "abcd".match(re"abcd")
      doAssert not "abcd".match(re"abc")

    var m: RegexMatch
    result = matchImpl(s, pattern, m, {mfNoCaptures})

func match*(
  s: string,
  pattern: Regex,
  m: var RegexMatch,
  start = 0
): bool {.inline.} =
  const f: MatchFlags = {}
  result = matchImpl(s, pattern, m, f, start)

func match*(s: string, pattern: Regex): bool {.inline.} =
  var m: RegexMatch
  result = matchImpl(s, pattern, m, {mfNoCaptures})

func contains*(s: string, pattern: Regex): bool {.inline.} =
  ## search for the pattern anywhere
  ## in the string. It returns as soon
  ## as there is a match, even when the
  ## expression has repetitions
  runnableExamples:
    doAssert re"bc" in "abcd"
    doAssert re"(23)+" in "23232"
    doAssert re"^(23)+$" notin "23232"

  result = false
  var m: RegexMatch
  var i = 0
  var c: Rune
  while i < len(s):
    result = matchImpl(s, pattern, m, {mfShortestMatch, mfNoCaptures}, i)
    if result:
      break
    fastRuneAt(s, i, c, true)

func find*(
  s: string,
  pattern: Regex,
  m: var RegexMatch,
  start = 0
): bool {.inline.} =
  result = false
  var i = start
  var c: Rune
  while i < len(s):
    result = matchImpl(s, pattern, m, {mfShortestMatch, mfNoCaptures}, i)
    if result:
      result = matchImpl(s, pattern, m, {mfLongestMatch}, i)
      doAssert result
      break
    fastRuneAt(s, i, c, true)

iterator findAll*(
  s: string,
  pattern: Regex,
  start = 0
): RegexMatch {.inline.} =
  ## Find all non-overlapping matches
  var i = start
  var c: Rune
  var m: RegexMatch
  while i < len(s):
    if not find(s, pattern, m, i):
      break
    if i < m.boundaries.b+1:
      i = m.boundaries.b+1
    else:  # empty match
      fastRuneAt(s, i, c, true)
    yield m

func findAll*(
  s: string,
  pattern: Regex,
  start = 0
): seq[RegexMatch] {.inline.} =
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
    m.captures == @[@[0 .. 1]]
  doAssert match("aabc", re"(aa)(bc)", m) and
    m.captures == @[@[0 .. 1], @[2 .. 3]]
  doAssert match("ab", re"a(b|c)", m) and
    m.captures == @[@[1 .. 1]]
  doAssert match("ab", re"(ab)*", m) and
    m.captures == @[@[0 .. 1]]
  doAssert match("abab", re"(ab)*", m) and
    m.captures == @[@[0 .. 1, 2 .. 3]]
  doAssert match("ab", re"((a))b", m) and
    m.captures == @[@[0 .. 0], @[0 .. 0]]
  doAssert match("c", re"((ab)*)c", m) and
    m.captures == @[@[0 .. -1], @[]]
  doAssert match("aab", re"((a)*b)", m) and
    m.captures == @[@[0 .. 2], @[0 .. 0, 1 .. 1]]
  doAssert match("abbbbcccc", re"a(b|c)*", m) and
    m.captures == @[@[1 .. 1, 2 .. 2, 3 .. 3, 4 .. 4, 5 .. 5, 6 .. 6, 7 .. 7, 8 .. 8]]
  doAssert match("ab", re"(a*)(b*)", m) and
    m.captures == @[@[0 .. 0], @[1 .. 1]]
  doAssert match("ab", re"(a)*(b)*", m) and
    m.captures == @[@[0 .. 0], @[1 .. 1]]
  doAssert match("ab", re"(a)*b*", m) and
    m.captures == @[@[0 .. 0]]
  doAssert match("abbb", re"((a(b)*)*(b)*)", m) and
    m.captures == @[@[0 .. 3], @[0 .. 3], @[1 .. 1, 2 .. 2, 3 .. 3], @[]]
  doAssert match("aa", re"(a)+", m) and
    m.captures == @[@[0 .. 0, 1 .. 1]]
  doAssert match("abab", re"(ab)+", m) and
    m.captures == @[@[0 .. 1, 2 .. 3]]
  doAssert match("a", re"(a)?", m) and
    m.captures == @[@[0 .. 0]]
  doAssert match("ab", re"(ab)?", m) and
    m.captures == @[@[0 .. 1]]
  doAssert match("aaabbbaaa", re"(a*|b*)*", m) and
    m.captures == @[@[0 .. 2, 3 .. 5, 6 .. 8]]
  doAssert match("abab", re"(a(b))*", m) and
    m.captures == @[@[0 .. 1, 2 .. 3], @[1 .. 1, 3 .. 3]]
  doAssert match("aaanasdnasd", re"((a)*n?(asd)*)*", m) and
    m.captures == @[@[0 .. 6, 7 .. 10], @[0 .. 0, 1 .. 1, 2 .. 2], @[4 .. 6, 8 .. 10]]
  doAssert match("aaanasdnasd", re"((a)*n?(asd))*", m) and
    m.captures == @[@[0 .. 6, 7 .. 10], @[0 .. 0, 1 .. 1, 2 .. 2], @[4 .. 6, 8 .. 10]]
  doAssert match("abd", re"((ab)c)|((ab)d)", m) and
    m.captures == @[@[], @[], @[0 .. 2], @[0 .. 1]]
  doAssert match("aaa", re"(a*)", m) and
    m.captures == @[@[0 .. 2]]
  doAssert match("aaaa", re"(a*)(a*)", m) and
    m.captures == @[@[0 .. 3], @[4 .. 3]]
  doAssert match("aaaa", re"(a*?)(a*?)", m) and
    m.captures == @[@[0 .. -1], @[0 .. 3]]
  doAssert match("aaaa", re"(a)*(a)", m) and
    m.captures == @[@[0 .. 0, 1 .. 1, 2 .. 2], @[3 .. 3]]
  
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
    m.group(0) == @[0 .. 1, 2 .. 3])
  doAssert(
    "11222211".find(re"(22)+", m) and
    m.group(0) == @[2 .. 3, 4 .. 5])
  
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
    # unminimized == 7
    const re1 = re"(11)*+(111)*"
    doAssert re1.dfa.table.len == 4
    doAssert match("", re1)
    doAssert match("11", re1)
    doAssert match("111", re1)
    doAssert match("11111", re1)
    doAssert match("1111111", re1)
    doAssert match("1111111111", re1)
    doAssert not match("1", re1)
  block:
    # unminimized == 9
    const re1 = re"(11)+(111)*"
    doAssert re1.dfa.table.len == 6
    doAssert not match("", re1)
    doAssert match("11", re1)
    doAssert not match("111", re1)
    doAssert match("11111", re1)
  block:
    # unminimized == 7
    const re1 = re"(aabb)(ab)*"
    doAssert re1.dfa.table.len == 6
    doAssert match("aabb", re1)
    doAssert match("aabbab", re1)
    doAssert match("aabbabab", re1)
    doAssert not match("ab", re1)
    doAssert not match("aabbaba", re1)
  block:
    # unminimized == 4
    const re1 = re"0(10)*"
    doAssert re1.dfa.table.len == 3
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
