import unicode

import nodetype
import common

type
  Scanner*[T: Rune|Node] = ref object
    ## A scanner is a common
    ## construct for reading data
    raw*: string
    s*: seq[T]
    pos*: int

proc newScanner*[T](s: seq[T]): Scanner[T] =
  Scanner[T](s: s, pos: 0)

proc scan*[T](s: seq[T]): Scanner[T] =
  newScanner(s)

proc scan*(raw: string): Scanner[Rune] =
  Scanner[Rune](
    raw: raw,
    s: raw.toRunes,
    pos: 0)

iterator items*[T](sc: Scanner[T]): T =
  ## the yielded item gets consumed
  while sc.pos <= sc.s.high:
    inc sc.pos
    yield sc.s[sc.pos - 1]

iterator mitems*[T](sc: var Scanner[T]): var T =
  ## the yielded item gets consumed
  while sc.pos <= sc.s.high:
    inc sc.pos
    yield sc.s[sc.pos - 1]

proc finished*[T](sc: Scanner[T]): bool =
  sc.pos > sc.s.high

proc prev*[T](sc: Scanner[T]): T =
  sc.s[sc.pos - 1]

proc curr*[T](sc: Scanner[T]): T =
  sc.s[sc.pos]

proc next*[T](sc: Scanner[T]): T =
  ## return current item and consume it
  result = sc.s[sc.pos]
  inc sc.pos

proc peekImpl[T](sc: Scanner[T], default: T): T {.inline.} =
  ## same as ``curr`` except it
  ## returns a default/invalid value when
  ## the data is fully consumed
  if sc.pos > sc.s.high:
    default
  else:
    sc.s[sc.pos]

proc peek*(sc: Scanner[Rune]): Rune =
  peekImpl(sc, invalidRune)

proc peek*(sc: Scanner[Node]): Node =
  peekImpl(sc, initEOENode())

iterator peek*[T](sc: Scanner[T]): (T, T) =
  for s in sc:
    yield (s, sc.peek)

proc find*(sc: Scanner[Rune], r: Rune): int =
  ## return number of consumed chars.
  ## The scanner's position is not moved.
  ## ``-1`` is returned when char is not found
  result = 0
  let pos = sc.pos
  while true:
    if sc.finished:
      result = -1
      break
    if sc.curr == r:
      break
    discard sc.next()
    inc result
  sc.pos = pos
