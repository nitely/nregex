import ./parser
import ./exptransformation
import ./types
import ./nfatype
import ./nfa
when defined(regexDotDir):
  import ./dotgraph

func reImpl*(s: string): Regex {.inline.} =
  var groups: GroupsCapture
  let rpn = s
    .parse
    .transformExp(groups)
  let nfa = rpn.nfa2()
  result = Regex(
    nfa: nfa,
    groupsCount: groups.count,
    namedGroups: groups.names)
  when defined(regexDotDir):
    const regexDotDir {.strdefine.} = ""
    graphToFile(result, regexDotDir)

func reCt*(s: string): Regex {.compileTime.} =
  reImpl(s)
