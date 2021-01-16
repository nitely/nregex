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

import ./nregex/private/types
import ./nregex/private/common
import ./nregex/private/compiler
import ./nregex/private/nfatype
import ./nregex/private/nfamatch2

export
  Regex,
  RegexMatch,
  RegexError

func re*(
  s: string
): Regex {.raises: [RegexError].} =
  reImpl(s)

func match(s: string, reg: Regex, m: var RegexMatch): bool =
  matchImpl(s, reg, m)

func match(s: string, reg: Regex): bool =
  var m: RegexMatch
  result = matchImpl(s, reg, m)

when isMainModule:
  var m: RegexMatch

  doAssert match("abc", re"abc")
  doAssert match("aab", re"((a)*b)", m) and
    m.captures == @[0 .. 2, 1 .. 1]
  doAssert match("abbbbccccd", re"a(b|c)*d", m) and
    m.captures == @[8 .. 8]
  doAssert match("abbb", re"((a)*(b)*)", m) and
    m.captures == @[0 .. 3, 0 .. 0, 3 .. 3]
  doAssert match("abbb", re"((a(b)*)*(b)*)", m) and
    m.captures == @[0 .. 3, 0 .. 3, 3 .. 3, 0 .. -1]
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
    m.captures == @[0 .. -1, 0 .. -1]
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
    m.captures == @[0 .. 3, 0 .. 3, 3 .. 3, 0 .. -1]
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
    m.captures == @[0 .. -1, 0 .. -1, 0 .. 2, 0 .. 1]
  doAssert match("aaa", re"(a*)", m) and
    m.captures == @[0 .. 2]
  doAssert match("aaaa", re"(a*)(a*)", m) and
    m.captures == @[0 .. 3, 4 .. 3]
  doAssert match("aaaa", re"(a*?)(a*?)", m) and
    m.captures == @[0 .. -1, 0 .. 3]
  doAssert match("aaaa", re"(a)*(a)", m) and
    m.captures == @[2 .. 2, 3 .. 3]
