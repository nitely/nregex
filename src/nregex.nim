import tables
import sequtils
import unicode

import nregexpkg/parser
import nregexpkg/exptransformation
import nregexpkg/nfa
import nregexpkg/dfa
import nregexpkg/dfamacro

  #Regex* = dfa.Regex
    # a compiled regular expression
  #Captures* = dfa.Captures
type
  RegexMatch* = object
    ## result from matching operations
    captures: Captures
    namedGroups: OrderedTable[string, int16]
    boundaries*: Slice[int]

template reImpl(s: string): Regex =
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

#[
proc re*(s: static string): Regex =
  static:
    result = reImpl(s)
]#

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

proc group*(m: RegexMatch, groupName: string, text:string): seq[string] = 
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

proc clear(m: var RegexMatch) {.inline.} =
  if m.captures.len > 0:
    m.captures.setLen(0)
  if m.namedGroups.len > 0:
    m.namedGroups.clear()
  m.boundaries = 0 .. -1

proc match*(
  s: string,
  pattern: Regex,
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

  m.clear()
  const f: MatchFlags = {}
  result = matchImpl(s[start .. s.len-1], pattern, m.captures, f)

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
  var capts: Captures
  var i = 0
  var c: Rune
  while i < len(s):
    result = matchImpl(s, pattern, capts, {mfShortestMatch}, i)
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
    m.clear()
    result = matchImpl(s, pattern, m.captures, {mfLongestMatch}, i)
    if result:
      break
    fastRuneAt(s, i, c, true)

when isMainModule:
  var m: RegexMatch
  doAssert "abcd".match(re"abcd", m)
  doAssert not "abcd".match(re"abc", m)
  doAssert match("abc", re"abc", m)
  doAssert match("ab", re"a(b|c)", m)
  doAssert match("ac", re"a(b|c)", m)
  doAssert not match("ad", re"a(b|c)", m)
  doAssert match("abab", re"(ab)*", m)
  doAssert not match("ababc", re"(ab)*", m)
  doAssert match("bc", re"bc*", m)

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

#[
proc matchCapt(s: string, exp: Regex): (bool, Captures) {.inline.} =
  return matchImpl(s, exp)

proc match2*(s: string, exp: Regex): bool {.inline.} =
  let (matched, _) = matchCapt(s, exp)
  return matched

proc matchMacroCapt(s: string, exp: static Regex): (bool, Captures) {.inline.} =
  return matchImpl2(s, exp)

proc matchMacro*(s: string, exp: static Regex): bool {.inline.} =
  let (matched, _) = matchMacroCapt(s, exp)
  return matched

when isMainModule:
  const pat1 = re"abc"
  doAssert matchMacro("abc", pat1)
  const pat2 = re"\w"
  doAssert matchMacro("a", pat2)
  const pat3 = re"(aa)bc"
  doAssert matchMacroCapt("aabc", pat3) ==
    (true, @[@[0 .. 1]])
  const pat4 = re"((a(b)*)*(b)*)"
  doAssert matchMacroCapt("abbb", pat4) ==
    (true, @[@[0 .. 3], @[0 .. 3], @[1 .. 1, 2 .. 2, 3 .. 3], @[]])

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
]#
