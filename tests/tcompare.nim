## Compare the static and runtime TDFA
## matchers against the original
## engine (``nregex/private/old``), on random inputs.
## The original engine keeps every capture of a group,
## the last one is compared. ``find`` is not compared,
## the original engine returns the longest match. Loops
## whose body can match empty are not compared either,
## the original engine skips the empty iteration, while
## PCRE (and nregex) take it; see ``tpcre``.

import std/[random, macros, strutils]
import pkg/nregex
from pkg/nregex/private/old/oldnregex as old import nil

const alphabet = [
  "a", "b", "c", "d", "s", "o", "l", "0", "5", "-", " ", "\n", "_",
  "á", "弢", "٣", "\xff", "\t", " ", "x", "é"]

proc genInputs(): seq[string] =
  var r = initRand(7)
  for n in 0 .. 7:
    for k in 0 ..< 200:
      var s = ""
      for _ in 0 ..< n:
        s.add alphabet[r.rand(alphabet.high)]
      result.add s
  result.add ["", "650-253-0001", "aaasolbbb", "sol", "abab",
    "aaanasdnasd", "abbbbccccd", "aabcd", "abd", "aaaa", "abcd",
    "a b c", "aa bb", "ab\nab", "\na\n"]

let inputs = genInputs()

func lastCaptures(m: old.RegexMatch): seq[Slice[int]] =
  for g in m.captures:
    result.add(if g.len == 0: reNonCapture else: g[^1])

var fails, checked = 0

macro compareAll(pats: static openArray[string]): untyped =
  result = newStmtList()
  for p in pats:
    let pl = newLit p
    result.add quote do:
      block:
        let oldRe = old.re(`pl`)
        let rtRe = re(`pl`)
        for s in inputs:
          var m1, m3: RegexMatch
          var m2: old.RegexMatch
          let a = match(s, re(`pl`), m1)
          let b = old.match(s, oldRe, m2)
          let a2 = match(s, re(`pl`))
          let a3 = match(s, rtRe, m3)
          let a4 = match(s, rtRe)
          inc checked
          if a != b or a != a2 or a != a3 or a != a4 or (a and (
              m1.boundaries != m2.boundaries or
              m1.captures != m2.lastCaptures or
              m3.boundaries != m2.boundaries or
              m3.captures != m2.lastCaptures)):
            inc fails
            if fails <= 20:
              echo "MISMATCH ", `pl`, " ", s.escape,
                " static=", a, "/", a2, " runtime=", a3, "/", a4, " old=", b,
                "\n  static =", m1.captures, "\n  runtime=", m3.captures,
                "\n  old    =", m2.lastCaptures

compareAll([
  # captures
  r"(a)*", r"((a)*b)", r"a(b|c)*d", r"((a)*(b)*)", r"((a(b)*)*(b)*)",
  r"(a)+", r"(ab)+", r"(a)?", r"(ab)?", r"(aa)bcd",
  r"(aa)(bc)", r"a(b|c)", r"(ab)*", r"((a))b", r"((ab)*)c", r"(a*)(b*)",
  r"(a)*(b)*", r"(a)*b*", r"(a(b))*", 
  r"((ab)c)|((ab)d)", r"(a*)", r"(a*)(a*)", r"(a*?)(a*?)", r"(a)*(a)",
  r"(a+?)(a*)", r"(a|ab)(c|bcd)?", r"(a|ab)(c|bcd)(d*)",
  r"([0-9]+)-([0-9]+)-([0-9]+)", r"(\w*)sol(\w*)", r"(\w+)\s(\w+)",
  r"(\s*)(\S+)", r"([^a]*)(a*)", r"(\d+)?(\D*)", r"(\W)(\w*)",
  r"(\p{L}+)(.*)", r"(.)*", r"(?s)(.)*", r"(.*)(.*)", r"(.*?)(.*)",
  r"(x?)(x?)(x?)", r"(?:(a)|b)*", r"(?:(a)|(b))*", r"(a|b)*?(b)",
  r"(a{2,3})(a*)", r"((a)|(b))+", r"(?P<n>a+)(b)", r"(?i)(A+)(b*)",
  r"([[:alpha:]]+)(-?)", r"(\w)*(\s)", r"([a-c]+?)(c*)", r"(弢*)(á?)",
  r"([\s\d]*)(.)", r"(?:(\w+)\s?)+", r"(a)|(b)|(c)", r"(a|b|ab)*(c)",
  r"\s+", r"[^a]+", r"\S*\s", r"\pL+", r"(\D+)(\d)",
  # assertions
  r"(a)\b", r"\b(\w+)\b", r"(\w+)\b.*", r"(.*)\b(\w*)", r"\B(\w*)",
  r"(a*)\B(a*)", r"^(a*)$", r"(?m)(a*)$\n?(a*)", r"(?m)^(\w*)", r"(?m)(.*)$(\s*)",
  r"\A(a|b)*\z", r"(a)(?=b)(\w)", r"(\w)(?=b)", r"(?s)(.*)(?=a)(.)",
  r"(\b\w\b|\s)*", r"(?u)\b(\w)", r"(?-u)\b(\w+)\b", r"(?-u)(\w)\B(\w)",
  r"(é)\b", r"\b(弢)", r"(.)\b(.)", r"(.)\B(.)"])

echo "checked=", checked, " fails=", fails
doAssert fails == 0
