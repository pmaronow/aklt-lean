module
public import AKLT.Blueprint.Q.NodesEnergy

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators

namespace AKLT.W.Q059

open AKLT.Defs

private theorem weighted_error_decomposition {Ω : Type} [Fintype Ω]
    (p : Weight Ω) (hp : ∑ x, p x = 1) (f : Ω → ℂ) (c : ℂ) :
    (∑ x, p x * Complex.normSq (f x - c)) =
      variance p f + Complex.normSq (complexMean p f - c) := by
  classical
  let μ := complexMean p f
  have hmean : ∑ x, (p x : ℂ) * (f x - μ) = 0 := by
    dsimp [μ, complexMean]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    have hpc : (∑ x, (p x : ℂ)) = 1 := by exact_mod_cast hp
    simp [hpc]
  have hcross :
      ∑ x, p x * (2 * ((f x - μ) * star (μ - c)).re) = 0 := by
    have hreal :
        (∑ x, ((p x : ℂ) * (f x - μ)) * star (μ - c)).re =
          ∑ x, p x * ((f x - μ) * star (μ - c)).re := by
      rw [Complex.re_sum]
      apply Finset.sum_congr rfl
      intro x hx
      simp [mul_assoc, Complex.mul_re]
    have hfactor :
        (∑ x, ((p x : ℂ) * (f x - μ)) * star (μ - c)) =
          (∑ x, (p x : ℂ) * (f x - μ)) * star (μ - c) := by
      rw [Finset.sum_mul]
    calc
      _ = 2 * (∑ x, p x * ((f x - μ) * star (μ - c)).re) := by
        calc
          _ = ∑ x, 2 * (p x * ((f x - μ) * star (μ - c)).re) := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
          _ = _ := by rw [Finset.mul_sum]
      _ = 2 * (∑ x, ((p x : ℂ) * (f x - μ)) * star (μ - c)).re := by
        rw [hreal]
      _ = 0 := by rw [hfactor, hmean]; simp
  calc
    (∑ x, p x * Complex.normSq (f x - c)) =
        (∑ x, p x * Complex.normSq (f x - μ)) +
          (∑ x, p x * Complex.normSq (μ - c)) +
          (∑ x, p x * (2 * ((f x - μ) * star (μ - c)).re)) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      have heq : f x - c = (f x - μ) + (μ - c) := by ring
      rw [heq, Complex.normSq_add]
      rw [starRingEnd_apply]
      ring
    _ = variance p f + Complex.normSq (μ - c) := by
      rw [hcross]
      simp
      rw [show (∑ x, p x * Complex.normSq (μ - c)) =
          (∑ x, p x) * Complex.normSq (μ - c) by rw [Finset.sum_mul]]
      rw [hp]
      simp [μ, variance]

theorem main : AKLT.Blueprint.Q.DensityVarianceStatement := by
  classical
  intro Ω hΩ p q hp hq M hM hdom f
  let μ := complexMean p f
  have hqerr :
      variance q f ≤ ∑ σ, q σ * Complex.normSq (f σ - μ) := by
    rw [weighted_error_decomposition q hq.2 f μ]
    exact le_add_of_nonneg_right (Complex.normSq_nonneg _)
  have hperr :
      (∑ σ, p σ * Complex.normSq (f σ - μ)) = variance p f := by
    simp [μ, variance]
  calc
    variance q f ≤ ∑ σ, q σ * Complex.normSq (f σ - μ) := hqerr
    _ ≤ ∑ σ, M * (p σ * Complex.normSq (f σ - μ)) := by
      apply Finset.sum_le_sum
      intro σ hσ
      simpa [mul_assoc] using
        (mul_le_mul_of_nonneg_right (hdom σ) (Complex.normSq_nonneg (f σ - μ)))
    _ = M * variance p f := by rw [← Finset.mul_sum, hperr]

end AKLT.W.Q059
