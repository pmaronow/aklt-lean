import AKLT.Blueprint.Gap.NodesFinite

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Gap

namespace AKLT.W.GAP017

local instance (α : Type) : DecidableEq α := Classical.decEq α

theorem conditionalExpectation_eq_of_agree {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] (p : Weight (Config S)) (U : Finset ι)
    (f : Config S → ℂ) (σ τ : Config S) (hστ : AgreeOutside U σ τ) :
    conditionalExpectation p U f σ = conditionalExpectation p U f τ := by
  classical
  have hrel (ρ : Config S) : AgreeOutside U σ ρ ↔ AgreeOutside U τ ρ := by
    constructor
    · intro hσρ x hx
      rw [← hστ x hx]
      exact hσρ x hx
    · intro hτρ x hx
      rw [hστ x hx]
      exact hτρ x hx
  have hnum :
      (∑ ρ, if AgreeOutside U σ ρ then (p ρ : ℂ) * f ρ else 0) =
      (∑ ρ, if AgreeOutside U τ ρ then (p ρ : ℂ) * f ρ else 0) := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    by_cases h : AgreeOutside U σ ρ
    · have ht : AgreeOutside U τ ρ := (hrel ρ).1 h
      simp [h, ht]
    · have ht : ¬ AgreeOutside U τ ρ := fun ht => h ((hrel ρ).2 ht)
      simp [h, ht]
  have hden :
      (∑ ρ, if AgreeOutside U σ ρ then (p ρ : ℂ) else 0) =
      (∑ ρ, if AgreeOutside U τ ρ then (p ρ : ℂ) else 0) := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    by_cases h : AgreeOutside U σ ρ
    · have ht : AgreeOutside U τ ρ := (hrel ρ).1 h
      simp [h, ht]
    · have ht : ¬ AgreeOutside U τ ρ := fun ht => h ((hrel ρ).2 ht)
      simp [h, ht]
  unfold conditionalExpectation
  rw [hnum, hden]

/-- The finite weighted least-squares identity, also for complex functions. -/
theorem weighted_sq_decomp {Ω : Type} [Fintype Ω] (p : Weight Ω)
    (hp : Probability p) (f : Ω → ℂ) (z : ℂ) :
    (∑ x, p x * Complex.normSq (f x - z)) =
      variance p f + Complex.normSq (complexMean p f - z) := by
  classical
  let m := complexMean p f
  have hm : (∑ x, (p x : ℂ) * f x) = m := rfl
  have hmass : ∑ x, p x = 1 := hp.2
  have hcross (w : ℂ) :
      (∑ x, p x * (f x * star w).re) = (m * star w).re := by
    calc
      (∑ x, p x * (f x * star w).re) =
          (∑ x, (((p x : ℂ) * f x) * star w).re) := by
            apply Finset.sum_congr rfl
            intro x hx
            simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
            ring
      _ = ((∑ x, (p x : ℂ) * f x) * star w).re := by
            rw [← Complex.re_sum]
            rw [Finset.sum_mul]
      _ = (m * star w).re := by rw [hm]
  have hcross2 (w : ℂ) :
      (∑ x, p x * (2 * (f x * star w).re)) = 2 * (m * star w).re := by
    calc
      (∑ x, p x * (2 * (f x * star w).re)) =
          2 * (∑ x, p x * (f x * star w).re) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x hx
            ring
      _ = 2 * (m * star w).re := by rw [hcross]
  have hcross2' (w : ℂ) :
      (∑ x, p x * (2 * (f x * (starRingEnd ℂ) w).re)) =
        2 * (complexMean p f * (starRingEnd ℂ) w).re := by
    simpa [m] using hcross2 w
  have hweight (w : ℂ) : (∑ x, p x * Complex.normSq w) = Complex.normSq w := by
    calc
      (∑ x, p x * Complex.normSq w) = (∑ x, p x) * Complex.normSq w := by
        rw [Finset.sum_mul]
      _ = Complex.normSq w := by rw [hmass]; ring
  have hvar : variance p f =
      (∑ x, p x * Complex.normSq (f x)) - Complex.normSq (complexMean p f) := by
    unfold variance
    simp_rw [Complex.normSq_sub]
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hweight (complexMean p f), hcross2' (complexMean p f)]
    have hmnorm :
        (complexMean p f * (starRingEnd ℂ) (complexMean p f)).re =
          Complex.normSq (complexMean p f) := by
      simp [Complex.mul_re, Complex.normSq_apply]
    rw [hmnorm]
    ring
  simp_rw [Complex.normSq_sub]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hweight z, hcross2' z, hvar]
  ring

end AKLT.W.GAP017
