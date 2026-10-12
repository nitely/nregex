## Public types

import std/tables

import tdfa

const nonCapture* = -1 .. -2
  ## capture of a group that did not match

type
  RegexFlag* = enum
    reAscii
  Regex* = object
    ## a compiled regular expression
    tdfa*: Tdfa  ## anchored at start and end
    tdfaFind*: Tdfa  ## leftmost-first search
    groupsCount*: int16
    namedGroups*: OrderedTable[string, int16]
    flags*: set[RegexFlag]
  MatchFlag* = enum
    mfNoCaptures
  MatchFlags* = set[MatchFlag]
  Captures* = seq[Slice[int]]
    ## last capture of every group, ``nonCapture`` if none
  RegexMatch* = object
    ## result from matching operations
    captures*: Captures
    namedGroups*: OrderedTable[string, int16]
    boundaries*: Slice[int]

func clear*(m: var RegexMatch) {.inline.} =
  if m.captures.len > 0:
    m.captures.setLen(0)
  if m.namedGroups.len > 0:
    m.namedGroups.clear()
  m.boundaries = 0 .. -1
