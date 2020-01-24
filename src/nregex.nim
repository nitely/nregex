import nregexpkg/parser
import nregexpkg/exptransformation
import nregexpkg/nfa
import nregexpkg/dfa

#type
#  Regex* = dfa.Regex
#  Captures* = dfa.Captures

proc re*(s: string): Regex =
  var groups: GroupsCapture
  var transitions: Transitions
  let dfa = s
    .parse
    .transformExp(groups)
    .nfa(transitions)
    .dfa2
  result = Regex(
    dfa: dfa,
    transitions: transitions,
    groupsCount: groups.count,
    namedGroups: groups.names)

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
