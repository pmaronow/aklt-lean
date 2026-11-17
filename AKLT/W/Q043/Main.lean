module
public import AKLT.Blueprint.Q.NodesQuantum

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Challenge AKLT.Blueprint.Q

namespace AKLT.W.Q043

theorem main : AKLT.Blueprint.Q.GroundTransformStatement := by
  intro L N κ hB hEval hLaw
  have hnorm : ‖B L N‖ ≠ 0 := norm_ne_zero_iff.mpr hB
  have hnormC : (‖B L N‖ : ℂ) ≠ 0 := by
    exact_mod_cast hnorm
  constructor
  · intro f
    change (∑ σ, torusReference L N σ *
        Complex.normSq (groundTransform κ f σ)) =
      ∑ σ, torusLaw L N κ σ * Complex.normSq (f σ)
    apply Finset.sum_congr rfl
    intro σ hσ
    rw [hLaw σ]
    unfold groundTransform
    rw [Complex.normSq_div, Complex.normSq_mul, Complex.normSq_ofReal]
    field_simp [hnorm]
  constructor
  · intro ψ
    funext σ
    unfold groundTransform groundQuotient
    field_simp [hnormC, hEval σ]
  · intro f σ
    unfold groundTransform
    field_simp [hnormC, hEval σ]

end AKLT.W.Q043
