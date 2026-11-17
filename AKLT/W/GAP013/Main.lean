module
public import AKLT.Blueprint.Gap.NodesFinite

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section

open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Gap

namespace AKLT.W.GAP013

theorem main : AKLT.Blueprint.Gap.NormalizedInteractionStatement := by
  classical
  intro ι hι hdec S hSfin hSnon π hπ ψ lo hi Z hlo hhi hψ hZ hZeq
  let q : Config S → ℝ := fun σ => ∏ x, π x (σ x)
  have hqpos : ∀ σ, 0 < q σ := by
    intro σ
    dsimp [q]
    exact Finset.prod_pos fun x hx => (hπ x).1 (σ x)
  have hqsum : ∑ σ, q σ = 1 := by
    dsimp [q]
    rw [← Fintype.prod_sum]
    have hnorm : ∀ x, (∑ a, π x a) = 1 := fun x => (hπ x).2
    simp_rw [hnorm]
    simp
  have hψpos : ∀ σ, 0 < ψ σ := by
    intro σ
    exact lt_of_lt_of_le hlo (hψ σ).1
  have hzsum : Z = ∑ σ, q σ * ψ σ := by
    simpa [expectation, q] using hZeq
  constructor
  · constructor
    · intro σ
      change 0 < q σ * ψ σ / Z
      exact div_pos (mul_pos (hqpos σ) (hψpos σ)) hZ
    · change (∑ σ, q σ * ψ σ / Z) = 1
      rw [← Finset.sum_div]
      rw [← hzsum]
      exact div_self (ne_of_gt hZ)
  · intro σ
    constructor
    · change (lo / Z) * q σ ≤ q σ * ψ σ / Z
      calc
        (lo / Z) * q σ = (lo * q σ) / Z := by ring
        _ ≤ (q σ * ψ σ) / Z := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hZ)
          calc
            lo * q σ = q σ * lo := by ring
            _ ≤ q σ * ψ σ := mul_le_mul_of_nonneg_left (hψ σ).1 (le_of_lt (hqpos σ))
    · change q σ * ψ σ / Z ≤ (hi / Z) * q σ
      calc
        q σ * ψ σ / Z ≤ (hi * q σ) / Z := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hZ)
          calc
            q σ * ψ σ ≤ q σ * hi := mul_le_mul_of_nonneg_left (hψ σ).2 (le_of_lt (hqpos σ))
            _ = hi * q σ := by ring
        _ = (hi / Z) * q σ := by ring

end AKLT.W.GAP013

#print axioms AKLT.W.GAP013.main
