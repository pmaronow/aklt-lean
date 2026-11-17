module
public import AKLT.Cert.H1.Production.Leaves

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H1C030

theorem main : AKLT.Cert.H1.Production.Leaves.representativesAppend := by
  intro rs
  induction rs with
  | nil =>
      intro ss hrs hss
      exact hss
  | cons r rs ih =>
      intro ss hrs hss
      exact ⟨hrs.1, hrs.2.1, hrs.2.2.1, ih ss hrs.2.2.2 hss⟩

#print axioms AKLT.W.H1C030.main

end AKLT.W.H1C030
