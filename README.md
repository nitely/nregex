# nregex

[![licence](https://img.shields.io/github/license/nitely/nregex.svg?style=flat-square)](https://raw.githubusercontent.com/nitely/nregex/master/LICENSE)

This is currently a PoC for a DFA that supports submatches extraction. The match time complexity is linear in length of the text to match. [Read the article](https://nitely.github.io/2020/01/19/a-dfa-for-submatches-extraction.html) if you are interested in the implementation.

> [!WARNING]
> Pls use [nim-regex](https://github.com/nitely/nim-regex) for anything serious, instead of this package.

## Install

```
nimble install nregex
```

# Compatibility

Nim +1.0.4

## Usage

```nim
import pkg/nregex

var m: RegexMatch
doAssert match("abc", re"abc", m)
doAssert match("ab", re"a(b|c)", m)

doAssert match("aabcd", re"(aa)bcd", m)
doAssert m.group(0) == @[0 .. 1]
doAssert match("aab", re"((a)*b)", m)
doAssert m.group(0) == @[0 .. 2]
doAssert m.group(1) == @[0 .. 0, 1 .. 1]

doAssert "abcd".find(re"bc", m)
doAssert "2222".find(re"(22)*", m)
doAssert m.group(0) == @[0 .. 1, 2 .. 3]

doAssert re"bc" in "abcd"
doAssert re"(23)+" in "112323211"
```

## Docs

[Read the docs](https://nitely.github.io/nregex/)

## Benchmarks

The following benchmarks show nregex is up to 22 times faster than PCRE. However, when the RE contains capture groups, PCRE is about 4 times faster than nregex.

|  | relative | time/iter | iters/s | regex | text
| --- | --- | --- | --- | --- | ---
CPU | | 294.85ps | 3.39G
PCRE | | 1.10ms | 912.11 | ^\w\*sol\w\*$ | (a\*100000)sol(b\*100000)
nregex | 739.52% | 148.25us | 6.75K
PCRE | | 174.87ns | 5.72M | ^[0-9]+-[0-9]+-[0-9]+$ | 650-253-0001
nregex | 2280.84% | 7.67ns | 130.43M
PCRE | | 179.23ns | 5.58M | ^[0-9]+..+$ | 650-253-0001
nregex | 1447.15% | 12.38ns | 80.74M

## Tests

```
nimble test
```

## LICENSE

MIT
