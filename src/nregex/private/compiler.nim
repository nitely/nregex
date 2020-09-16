
import std/tables
import std/sequtils

import nregex/private/[
  parser,
  exptransformation,
  nfa,
  dfa,
  dfamatch
]

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
