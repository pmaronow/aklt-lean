module
public import AKLT.Blueprint.Q.NodesQuantum

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Challenge AKLT.Blueprint.Q

namespace AKLT.W.Q046

private theorem scalarPolarization (z u : ℂ) :
    star z * u =
      (((‖z + u‖ : ℂ) ^ 2 - (‖z - u‖ : ℂ) ^ 2 +
        ((‖z - Complex.I • u‖ : ℂ) ^ 2 - (‖z + Complex.I • u‖ : ℂ) ^ 2) * Complex.I) / 4) := by
  simpa [inner, mul_comm] using (inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) (E := ℂ) z u)

private theorem weightedPolarization {Ω : Type*} [Fintype Ω] (w : Weight Ω)
    (f g : Ω → ℂ) :
    weightedInner w f g =
      (((weightedNorm w (f + g) : ℂ) - weightedNorm w (f - g) +
        ((weightedNorm w (f - Complex.I • g) : ℂ) -
          weightedNorm w (f + Complex.I • g)) * Complex.I) / 4) := by
  classical
  unfold weightedInner weightedNorm
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Complex.ofReal_sum, Complex.ofReal_mul]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.sum_mul,
    ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a ha
  have hs := scalarPolarization (f a) (g a)
  simp only [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq] at hs ⊢
  linear_combination (w a : ℂ) * hs

theorem main : AKLT.Blueprint.Q.WeightedPolarizationStatement := by
  intro ι Ω instι instΩ w E h ψ φ
  rw [weightedPolarization]
  have hadd : E ψ + E φ = E (ψ + φ) := by simp
  have hsub : E ψ - E φ = E (ψ - φ) := by simp
  have hiSub : E ψ - Complex.I • E φ = E (ψ - Complex.I • φ) := by simp
  have hiAdd : E ψ + Complex.I • E φ = E (ψ + Complex.I • φ) := by simp
  rw [hadd, hsub, hiSub, hiAdd, h, h, h, h]
  simpa using
    (inner_eq_sum_norm_sq_div_four (𝕜 := ℂ)
      (E := EuclideanSpace ℂ ι) ψ φ).symm

end AKLT.W.Q046
