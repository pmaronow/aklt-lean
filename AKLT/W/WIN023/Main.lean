module
public import AKLT.Blueprint.Win.NodesTopology

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.WIN023

theorem main : AKLT.Blueprint.Win.TwoCrossingParityStatement := by
  classical
  intro A E hE e he f hf hnotE c hc
  unfold AKLT.Blueprint.Win.cutParity
  calc
    (∑ g ∈ E, c g) = c e := by
      apply Finset.sum_eq_single e
      · intro g hg hge
        have hgCut : g ∈ AKLT.Blueprint.Win.cutEdges A := hE hg
        have hgf : g ≠ f := by
          intro h
          subst g
          exact hnotE hg
        rw [hc g hgCut]
        simp [hge, hgf]
      · intro heNot
        exact False.elim (heNot he)
    _ = 1 := by
      rw [hc e (hE he)]
      simp

end AKLT.W.WIN023

#print axioms AKLT.W.WIN023.main
