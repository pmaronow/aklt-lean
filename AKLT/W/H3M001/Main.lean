module
public import AKLT.Cert.H2.Words
public import AKLT.Blueprint.H3.NodesAutomaton

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H3M001

/-- Raw successor closure for the frozen H3 automaton leaf. -/
theorem main : AKLT.Blueprint.H3.RawSuccessorStatement := by
  intro m _ w hw d hd
  exact AKLT.Cert.H2.successor_raw w d hw hd

#print axioms main

end AKLT.W.H3M001
