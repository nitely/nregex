import tables
import sequtils
import unicode

import nregexpkg/common
import nregexpkg/parser
import nregexpkg/exptransformation
import nregexpkg/nfa
import nregexpkg/dfa
import nregexpkg/dfamacro

type
  Regex* = dfa.Regex
    ## a compiled regular expression
  RegexMatch* = dfa.RegexMatch
  RegexError* = common.RegexError
    ## raised when the pattern
    ## is not a valid regex

template reImpl(s: untyped): Regex =
  var groups: GroupsCapture
  var transitions: Transitions
  let dfa = s
    .parse
    .transformExp(groups)
    .nfa(transitions)
    .dfa
  Regex(
    dfa: dfa,
    transitions: transitions,
    groupsCount: groups.count,
    namedGroups: groups.names)

proc re*(s: string): Regex =
  reImpl(s)

when not defined(forceRegexAtRuntime):
  proc re*(s: static string): static Regex =
    reImpl(s)

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

proc group*(m: RegexMatch, i: int): seq[Slice[int]] =
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

proc group*(m: RegexMatch, s: string): seq[Slice[int]] =
  ## return slices for a given named group.
  ## Use the iterator version if you care about performance
  m.group(m.namedGroups[s])

proc groupsCount*(m: RegexMatch): int =
  ## return the number of capturing groups
  runnableExamples:
    var m: RegexMatch
    doAssert "ab".match(re"(a)(b)", m)
    doAssert m.groupsCount == 2

  m.captures.len

proc groupNames*(m: RegexMatch): seq[string] =
  ## return the names of capturing groups.
  runnableExamples:
    let text = "hello world"
    var m: RegexMatch
    doAssert text.match(re"(?P<greet>hello) (?P<who>world)", m)
    doAssert m.groupNames() == @["greet", "who"]

  result = toSeq(m.namedGroups.keys)

proc group*(m: RegexMatch, groupName: string, text: string): seq[string] = 
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

proc groupFirstCapture*(m: RegexMatch, groupName: string, text: string): string =
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

proc groupLastCapture*(m: RegexMatch, groupName: string, text: string): string =
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

proc isInitialized*(re: Regex): bool =
  ## Check whether the regex has been initialized
  runnableExamples:
    var re: Regex
    doAssert not re.isInitialized
    re = re"foo"
    doAssert re.isInitialized

  re.dfa.table.len > 0

when not defined(forceRegexAtRuntime):
  proc match*(
    s: string,
    pattern: static Regex,
    m: var RegexMatch,
    start = 0
  ): bool =
    ## return a match if the whole string
    ## matches the regular expression. This
    ## is similar to ``find(text, re"^regex$")``
    ## but has better performance
    runnableExamples:
      var m: RegexMatch
      doAssert "abcd".match(re"abcd", m)
      doAssert(not "abcd".match(re"abc", m))

    when pattern.namedGroups.len > 0:
      const namedGroups = pattern.namedGroups
      m.namedGroups = namedGroups
    const f: MatchFlags = {}
    result = matchImpl(s, pattern, m, f, start)

proc match*(
  s: string,
  pattern: Regex,
  m: var RegexMatch,
  start = 0
): bool =
  const f: MatchFlags = {}
  result = matchImpl(s, pattern, m, f, start)

proc contains*(s: string, pattern: Regex): bool =
  ##  search for the pattern anywhere
  ##  in the string. It returns as soon
  ##  as there is a match, even when the
  ##  expression has repetitions. Use
  ##  ``re"^regex$"`` to match the whole
  ##  string instead of searching
  runnableExamples:
    doAssert(re"bc" in "abcd")
    doAssert(re"(23)+" in "23232")
    doAssert(re"^(23)+$" notin "23232")

  result = false
  var m: RegexMatch
  var i = 0
  var c: Rune
  while i < len(s):
    result = matchImpl(s, pattern, m, {mfShortestMatch}, i)
    if result:
      break
    fastRuneAt(s, i, c, true)

proc find*(
  s: string,
  pattern: Regex,
  m: var RegexMatch,
  start = 0
): bool =
  result = false
  var i = start
  var c: Rune
  while i < len(s):
    result = matchImpl(s, pattern, m, {mfLongestMatch}, i)
    if result:
      break
    fastRuneAt(s, i, c, true)

when isMainModule:
  var m: RegexMatch

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

  doAssert re"bc" in "abcd"
  doAssert re"(23)+" in "23232"
  doAssert re"^(23)+$" notin "23232"

  doAssert "abcd".find(re"bc", m)
  doAssert not "abcd".find(re"de", m)
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