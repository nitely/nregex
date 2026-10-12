## Benchmarks: PCRE (std/re) vs nregex (static/macro ``match``)
##
## Run with:
##   nim c -r -d:danger bench/bench.nim
##
## On Intel Skylake-derived CPUs, short benchmarks swing
## +-30% depending on code layout (JCC erratum). For stable
## numbers pin a core and pass the assembler mitigation:
##   nim c -d:danger --passC:-Wa,-mbranches-within-32B-boundaries \
##     -o:bin/bench bench/bench.nim && taskset -c 2 bin/bench
##
## Requires ``nimbench`` (``nimble install nimbench``) and libpcre.
## Texts are runtime values so the C compiler can not
## constant-fold the (fully inlined) static matchers.

from std/re import nil
import nimbench
import ../src/nregex

proc rt(s: string): string {.noinline.} =
  ## prevent the C compiler from seeing the text
  result = s

var solText = ""
for _ in 0 ..< 100000:
  solText.add "a"
solText.add "sol"
for _ in 0 ..< 100000:
  solText.add "b"
solText = rt(solText)

var dateText = rt("650-253-0001")

var uniText = ""
for _ in 0 ..< 10000:
  uniText.add "áéíóú"
uniText.add "sol"
uniText = rt(uniText)

template benchPair(name: untyped, text, pcreRe: untyped, body: untyped) =
  let pcrePattern = re.re(pcreRe)
  bench(`name Pcre`, m):
    var d: bool
    for i in 0 ..< m:
      d = re.match(text, pcrePattern)
    doNotOptimizeAway(d)
  benchRelative(`name Nregex`, m):
    var mm {.inject.}: RegexMatch
    var d: bool
    for i in 0 ..< m:
      d = body
    doNotOptimizeAway(d)

benchPair(sol, solText, r"^\w*sol\w*$"):
  match(solText, re"\w*sol\w*", mm)

benchPair(dates, dateText, r"^[0-9]+-[0-9]+-[0-9]+$"):
  match(dateText, re"[0-9]+-[0-9]+-[0-9]+", mm)

benchPair(dot, dateText, r"^[0-9]+..+$"):
  match(dateText, re"[0-9]+..+", mm)

benchPair(datesCapt, dateText, r"^([0-9]+)-([0-9]+)-([0-9]+)$"):
  match(dateText, re"([0-9]+)-([0-9]+)-([0-9]+)", mm)

benchPair(solCapt, solText, r"^(\w*)sol(\w*)$"):
  match(solText, re"(\w*)sol(\w*)", mm)

benchPair(unicode, uniText, r"(*UTF8)(*UCP)^\w*sol$"):
  match(uniText, re"\w*sol", mm)

when isMainModule:
  runBenchmarks()
