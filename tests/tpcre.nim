## Compare match, find and findAll against PCRE (std/re),
## on random inputs. Requires libpcre.
##
## PCRE runs in UTF-8 + UCP mode, so ``\w``, ``\s``, ``\b``
## are Unicode aware. ``$`` is translated to ``\z`` out of
## multi-line mode, since PCRE's ``$`` also matches before
## a final new line. Inputs only contain chars for which
## both engines agree on ``\w`` and ``\s``.
##
## Known difference: multi-line ``^`` matches after a
## new line at the end of the text, same as nim-regex,
## while PCRE does not; those cases are skipped.

import std/[random, strutils, unicode, tables]
from std/re as pcre import nil
import pkg/nregex

const alphabet = [
  "a", "b", "c", "s", "o", "l", "0", "5", "-", " ", "\n", "_",
  "á", "弢", "\t", " ", "x", "é"]

proc genInputs(): seq[string] =
  var r = initRand(11)
  for n in 0 .. 7:
    for k in 0 ..< 150:
      var s = ""
      for _ in 0 ..< n:
        s.add alphabet[r.rand(alphabet.high)]
      result.add s
  result.add ["", "650-253-0001", "aaasolbbb", "sol", "abab",
    "aabcd", "abd", "aaaa", "abcd", "a b c", "aa bb", "ab\nab", "\na\nb"]

let inputs = genInputs()

proc toPcre(p: string): string =
  result = "(*UTF8)(*UCP)"
  if "(?m)" in p:
    result.add p
  else:
    result.add p.replace("$", "\\z")

type PcreMatch = object
  bounds: Slice[int]
  captures: seq[Slice[int]]

proc pcreFind(s: string, p: pcre.Regex, groups, start: int): (bool, PcreMatch) =
  # std/re only sets groups up to the last matched one
  var ms = newSeq[tuple[first, last: int]](groups)
  for m in ms.mitems:
    m = (-1, 0)
  let (a, b) = pcre.findBounds(s, p, ms, start)
  if a == -1:
    return (false, PcreMatch())
  result[0] = true
  result[1].bounds = a .. b
  for (first, last) in ms:
    result[1].captures.add(if first == -1: reNonCapture else: first .. last)

var fails, checked = 0
var failsBy = initCountTable[string]()

template report(kind, p, s: string, body: untyped) =
  inc fails
  failsBy.inc(kind & " " & p)
  if failsBy[kind & " " & p] <= 2:
    echo "MISMATCH ", kind, " ", p, " ", s.escape
    body

proc compare(p: string, groups: int) =
  let r = nregex.re(p)
  let pFind = pcre.re(toPcre(p))
  let pMatch = pcre.re(toPcre("\\A(?:" & p & ")\\z"))
  for s in inputs:
    if "(?m)^" in p and s.endsWith("\n"):
      continue
    inc checked
    # match
    block:
      var m: RegexMatch
      let a = match(s, r, m)
      let (b, pm) = pcreFind(s, pMatch, groups, 0)
      if a != b or (a and m.captures != pm.captures):
        report("match", p, s):
          echo "  nregex=", a, " ", m.captures, "\n  pcre  =", b, " ", pm.captures
    # find
    block:
      var m: RegexMatch
      let a = find(s, r, m)
      let (b, pm) = pcreFind(s, pFind, groups, 0)
      if a != b or (a and (m.boundaries != pm.bounds or m.captures != pm.captures)):
        report("find", p, s):
          echo "  nregex=", a, " ", m.boundaries, " ", m.captures,
            "\n  pcre  =", b, " ", pm.bounds, " ", pm.captures
    # findAll, same empty match handling as nregex
    block:
      var a: seq[Slice[int]]
      for m in findAll(s, r):
        a.add m.boundaries
      var b: seq[Slice[int]]
      var i = 0
      while i <= s.len:
        let (found, pm) = pcreFind(s, pFind, groups, i)
        if not found:
          break
        b.add pm.bounds
        if pm.bounds.b+1 > pm.bounds.a:
          i = pm.bounds.b+1
        elif pm.bounds.a < s.len:
          i = pm.bounds.a + s.runeLenAt(pm.bounds.a)
        else:
          break
      if a != b:
        report("findAll", p, s):
          echo "  nregex=", a, "\n  pcre  =", b

const patterns = [
  # captures
  (r"(a)*", 1), (r"((a)*b)", 2), (r"a(b|c)*d", 1), (r"((a)*(b)*)", 3),
  (r"(a)+", 1), (r"(ab)+", 1), (r"(a)?", 1), (r"(aa)(bc)", 2),
  (r"(ab)*", 1), (r"((ab)*)c", 2), (r"(a*)(b*)", 2), (r"(a)*(b)*", 2),
  (r"(a(b))*", 2), (r"((ab)c)|((ab)d)", 4), (r"(a*)(a*)", 2),
  (r"(a*?)(a*?)", 2), (r"(a)*(a)", 2), (r"(a+?)(a*)", 2),
  (r"(a|ab)(c|bcd)?", 2), (r"(a|ab)(c|bcd)(d*)", 3),
  (r"([0-9]+)-([0-9]+)-([0-9]+)", 3), (r"(\w*)sol(\w*)", 2),
  (r"(\w+)\s(\w+)", 2), (r"(\s*)(\S+)", 2), (r"([^a]*)(a*)", 2),
  (r"(\d+)?(\D*)", 2), (r"(\W)(\w*)", 2), (r"(.)*", 1), (r"(?s)(.)*", 1),
  (r"(.*)(.*)", 2), (r"(.*?)(.*)", 2), (r"(x?)(x?)(x?)", 3),
  (r"(?:(a)|b)*", 1), (r"(?:(a)|(b))*", 2), (r"(a|b)*?(b)", 2),
  (r"(a{2,3})(a*)", 2), (r"((a)|(b))+", 3), (r"(?i)(A+)(b*)", 2),
  (r"([a-c]+?)(c*)", 2), (r"(弢*)(á?)", 2), (r"(?:(\w+)\s?)+", 1),
  (r"(a)|(b)|(c)", 3), (r"(a|b|ab)*(c)", 2), (r"\s+", 0), (r"[^a]+", 0),
  (r"a|ab", 0), (r"ab|a", 0), (r"a*?", 0), (r"a+?", 0),
  (r"(a*)*", 1), (r"(a*|b*)*", 1), (r"((a)*n?(asd)*)*", 3),
  (r"(?m)(^|a)*", 1), (r"(?m)($|b)*.*", 1), (r"(a*)*b", 1), (r"((a*)*)*", 2),
  # assertions
  (r"(a)\b", 1), (r"\b(\w+)\b", 1), (r"(\w+)\b.*", 1), (r"\B(\w*)", 1),
  (r"(a*)\B(a*)", 2), (r"^(a*)$", 1), (r"(?m)^(\w*)", 1),
  (r"(?m)(\w*)$", 1), (r"\A(a|b)*\z", 1), (r"(a)(?=b)(\w)", 2),
  (r"\b", 0), (r"\B", 0), (r"^", 0), (r"$", 0), (r"(?m)^", 0),
  (r"(?m)$", 0), (r"(.)\b(.)", 2), (r"(.)\B(.)", 2)]

for (p, groups) in patterns:
  compare(p, groups)

for k, v in failsBy:
  echo v, " ", k
echo "checked=", checked, " fails=", fails
doAssert fails == 0
