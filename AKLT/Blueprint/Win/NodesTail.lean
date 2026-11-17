module
public import AKLT.Blueprint.Win.Defs

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.Blueprint.Win

/-- `t:cutMOS`, sec5-window.tex:714–724. Write θ^(s/12−1) using exp(log θ·(s/12−1)), use (2u+1)²≤9u² and u=s⁴, then exp(r)≥r¹⁰/10! for r>0. -/
def TailExponentialStatement : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ u : ℕ, 1 ≤ u →
    tailCost θ u ≤ tailConstant θ * shellSpacing u ^ (-2 : ℤ)

/-- `t:cutMOS`, sec5-window.tex:725–733. Take a natural ceiling dominating 390⁴, K², and one. Positivity of K and s then gives K/s²≤1 uniformly at all larger integer radii. -/
def TailThresholdStatement : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 →
    (∀ u : ℕ, 1 ≤ u → tailCost θ u ≤ tailConstant θ * shellSpacing u ^ (-2 : ℤ)) →
    ∃ M : ℕ, 1 ≤ M ∧ geometryThreshold 64 ≤ M ∧
      ∀ u : ℕ, M ≤ u → tailCost θ u ≤ 1

/-- `t:cutMOS`, sec5-window.tex:704–706,770–771. All displayed terms are nonnegative because A≥2, θ>0 and 1−θ>0. -/
def CutCostNonnegativeStatement : Prop :=
  ∀ A θ : ℝ, 2 ≤ A → 0 < θ → θ < 1 → 0 ≤ cutCost A θ

theorem cutCostNonnegative : CutCostNonnegativeStatement := by
  intro A θ hA hθ hθ1
  have hA0 : 0 ≤ A := by linarith
  have hden : 0 ≤ 1 - θ := by linarith
  unfold cutCost
  positivity

#print axioms cutCostNonnegative

/-- `t:cutMOS`, sec5-window.tex:746–755. Substitute the two cut-sum bounds and the tail≤1 estimate. Positive θ permits θ^(-3)θ⁻¹=θ^(-4); preserve the retained seed term 1+4A. -/
def WindowCostArithmeticStatement : Prop :=
  ∀ A θ raw thick e tail : ℝ, 2 ≤ A → 0 < θ → θ < 1 →
    raw ≤ nearCost θ + tail → tail ≤ 1 → thick ≤ 5 * θ⁻¹ * raw →
    |e| ≤ 1 + 4 * A + 2 * A * θ ^ (-3 : ℤ) * thick → |e| ≤ cutCost A θ

theorem windowCostArithmetic : WindowCostArithmeticStatement := by
  intro A θ raw thick e tail hA hθ hθ1 hr ht hth he
  have hA0 : 0 ≤ A := by linarith
  have hcoef : 0 ≤ 2 * A * θ ^ (-3 : ℤ) := by positivity
  have hmul : θ ^ (-3 : ℤ) * θ⁻¹ = θ ^ (-4 : ℤ) := by
    rw [zpow_neg, zpow_neg]
    simp only [zpow_ofNat, ← mul_inv_rev]
    congr 1
    ring
  have hu : |e| ≤ 1 + 4 * A + 2 * A * θ ^ (-3 : ℤ) *
      (5 * θ⁻¹ * (nearCost θ + 1)) := by
    apply he.trans
    gcongr
    exact hth.trans (mul_le_mul_of_nonneg_left (hr.trans (by linarith)) (by positivity))
  calc
    |e| ≤ 1 + 4 * A + 2 * A * θ ^ (-3 : ℤ) *
        (5 * θ⁻¹ * (nearCost θ + 1)) := hu
    _ = 1 + 4 * A + 10 * A * (θ ^ (-3 : ℤ) * θ⁻¹) * (nearCost θ + 1) := by ring
    _ = cutCost A θ := by rw [hmul]; rfl

#print axioms windowCostArithmetic

end AKLT.Blueprint.Win
