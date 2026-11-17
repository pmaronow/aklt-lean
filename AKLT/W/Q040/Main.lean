module
public import AKLT.Blueprint.Q.NodesQuantum

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Challenge AKLT.Blueprint.Q

namespace AKLT.W.Q040

 theorem main : AKLT.Blueprint.Q.GroundProductWeightStatement := by
  classical
  intro L N κ hEval hBond σ
  rw [hEval σ]
  have hnorm : Complex.normSq
      (∏ e : Bond L N,
        determinant (frameSpinor (κ e.1) (σ e.1))
          (frameSpinor (κ (nextSite e.1 e.2)) (σ (nextSite e.1 e.2)))) =
      ∏ e : Bond L N,
        Complex.normSq (determinant (frameSpinor (κ e.1) (σ e.1))
          (frameSpinor (κ (nextSite e.1 e.2)) (σ (nextSite e.1 e.2)))) := by
    simp only [map_prod]
  rw [hnorm]
  simp_rw [hBond]
  simp [torusReference, torusWeight, groundScale, Finset.prod_div_distrib]
  field_simp

#print axioms AKLT.W.Q040.main

end AKLT.W.Q040
