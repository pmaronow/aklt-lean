module
public import CertData.H3.Bridge.Production

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H3C049

theorem main : CertData.H3.Bridge.DecodeDataLeaf := by
  intro c
  rfl

#print axioms AKLT.W.H3C049.main

end AKLT.W.H3C049
