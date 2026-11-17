module
public import AKLT.W.GAP037.Weights

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Challenge AKLT.Blueprint.Gap

namespace AKLT.W.GAP037

/-- The local lifted parity gauge transports the conditional torus law to the plane law. -/
theorem main : AKLT.Blueprint.Gap.BoxGaugeLawStatement := by
  intro hPositive L N M hM hL hN κ hκ a C hB σ
  have hZ : (∑ τ, torusWeight L N κ τ) ≠ 0 :=
    ne_of_gt (Finset.sum_pos (fun τ _ => torusWeight_pos hPositive κ hκ τ) Finset.univ_nonempty)
  obtain ⟨c,hc,hWeight⟩ := liftedWeightFactorization hPositive hκ C hB
    (reduction_inj_halo L N M hL hN C.centre) σ
  intro ω
  change AKLT.Defs.normalize (planeWeight (κ ∘ reduction L N) (square C.centre M)
      (fun z => C.boundary σ z)) (C.change.configurations ω) =
    blockLaw (AKLT.Defs.normalize (torusWeight L N κ)) (torusSquare L N M a) σ ω
  rw [blockLaw_normalize_formula (torusWeight L N κ) hZ]
  exact (normalize_rescale_equiv C.change.configurations
    (fun ρ => torusWeight L N κ (insertBlock (torusSquare L N M a) σ ρ))
    (fun ρ => planeWeight (κ ∘ reduction L N) (square C.centre M)
      (fun z => C.boundary σ z) ρ) c (ne_of_gt hc) hWeight ω).symm

#print axioms main

end AKLT.W.GAP037
