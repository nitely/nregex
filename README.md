# nregex

[![licence](https://img.shields.io/github/license/nitely/nim-regex.svg?style=flat-square)](https://raw.githubusercontent.com/nitely/nregex/master/LICENSE)

This is currently a PoC for a DFA that supports submatches extraction. [Read the article](https://nitely.github.io/2020/01/19/a-dfa-for-submatches-extraction.html) if you are interested in the implementation.

## Install

```
nimble install nregex
```

# Compatibility

Nim +1.0.4

## Docs

[Read the docs](https://nitely.github.io/nregex/)

## Benchmarks

The following benchmarks show nregex is up to 7 times faster than PCRE. However, when the RE contains capture groups, PCRE is about 4 times faster than nregex.

|  | relative | time/iter | iters/s | regex | text
| --- | --- | --- | --- | --- | ---
CPU | | 294.85ps | 3.39G
PCRE | | 1.10ms | 912.11 | ^\w\*sol\w\*$ | (a\*100000)sol(b\*100000)
nregex | 739.52% | 148.25us | 6.75K
PCRE | | 152.28ns | 6.57M | ^[0-9]+-[0-9]+-[0-9]+$ | 650-253-0001
nregex | 420.48% | 36.22ns | 27.61M
PCRE | | 168.92ns | 5.92M | ^[0-9]+..+$ | 650-253-0001
nregex | 397.34% | 42.51ns | 23.52M

## Tests

```
nimble test
```

## LICENSE

MIT
