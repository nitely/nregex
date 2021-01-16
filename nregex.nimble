# Package

version = "0.0.4"
author = "Esteban Castro Borsani (@nitely)"
description = "A DFA based regex engine"
license = "MIT"
srcDir = "src"
skipDirs = @["tests", "docs"]

requires "nim >= 1.0.4"
requires "unicodedb >= 0.7.2"

task test, "Test":
  exec "nim c -r -o:bin/nregex src/nregex.nim"

task docs, "Docs":
  exec "nim doc --project -o:./docs ./src/nregex.nim"
