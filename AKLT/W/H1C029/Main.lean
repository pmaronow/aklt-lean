module
public import AKLT.Cert.H1.Production.Leaves

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H1C029

open AKLT.Cert.H1.Production

/-- Every accepted representative retains its checked input, covered pattern,
and the raw witness stored in the accepted-list predicate. -/
theorem main : AKLT.Cert.H1.Production.Leaves.representativeWitnessLookup := by
  change ∀ rs : List Representative,
    RepresentativesAccepted rs → ∀ r ∈ rs,
      inputCheck r.input = true ∧ (inputPattern r.input).Covered ∧
        RawWitness (inputPattern r.input)
  intro rs
  induction rs with
  | nil =>
      intro h r hr
      cases hr
  | cons a as ih =>
      intro h r hr
      rcases h with ⟨ha, hcovered, hwitness, htail⟩
      rcases List.mem_cons.mp hr with heq | hmem
      · subst r
        exact ⟨ha, hcovered, hwitness⟩
      · exact ih htail r hmem

#print axioms main

end AKLT.W.H1C029
