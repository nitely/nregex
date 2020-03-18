# Package

version = "0.0.3"
author = "Esteban Castro Borsani (@nitely)"
description = "A DFA based regex engine"
license = "MIT"
srcDir = "src"
skipDirs = @["tests"]

requires "nim >= 1.0.4"
requires "unicodedb >= 0.7.2"
requires "unicodeplus >= 0.5.0"

task test, "Test":
  exec "nim c -r -o:bin/nregex src/nregex.nim"
  exec "nim c -r tests/tests.nim"
  exec "nim c -r -d:forceRegexAtRuntime tests/tests.nim"
  # VM register limit error, works on devel,
  # well almost due to https://github.com/nim-lang/Nim/issues/13310
  #exec "nim c -d:runTestAtCT tests/tests.nim"
  exec "nim js -r -o:bin/nregex.js --styleCheck:off src/nregex.nim"
  exec "nim js -r --styleCheck:off tests/tests.nim"
  exec "nim js -r --styleCheck:off -d:forceRegexAtRuntime tests/tests.nim"

  # Test runnable examples
  exec "nim doc -o:./docs/ugh/ugh.html ./src/nregex.nim"

task docs, "Docs":
  exec "nim doc --project -o:./docs ./src/nregex.nim"
