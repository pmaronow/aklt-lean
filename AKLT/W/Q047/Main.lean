import AKLT.Blueprint.Q.NodesQuantum

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Challenge AKLT.Blueprint.Q

namespace AKLT.W.Q047

private theorem weightedNorm_eq_re_weightedInner
    {Ω : Type*} [Fintype Ω] (w : Weight Ω) (f : Ω → ℂ) :
    weightedNorm w f = (weightedInner w f f).re := by
  unfold weightedNorm weightedInner
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  have hns : (Complex.normSq (f σ) : ℂ) = star (f σ) * f σ := by
    simpa using Complex.normSq_eq_conj_mul_self (z := f σ)
  have heq : ((w σ * Complex.normSq (f σ) : ℝ) : ℂ) =
      (w σ : ℂ) * star (f σ) * f σ := by
    rw [Complex.ofReal_mul, hns]
    ring
  have hre := congrArg Complex.re heq
  simpa using hre

theorem main : AKLT.Blueprint.Q.GroundQuotientVarianceStatement := by
  classical
  intro L N κ hB hGround hLaw hInner ψ hOrth
  let r : ℂ := (‖B L N‖ : ℂ)
  have hnB : ‖B L N‖ ≠ 0 := norm_ne_zero_iff.mpr hB
  have hr : r ≠ 0 := by
    intro hr0
    dsimp [r] at hr0
    apply hnB
    exact_mod_cast hr0
  have hmean :
      complexMean (torusLaw L N κ) (groundQuotient κ ψ) =
        weightedInner (torusReference L N) (frameEval κ (B L N))
          (frameEval κ ψ) / r := by
    unfold complexMean weightedInner
    calc
      (∑ σ, (torusLaw L N κ σ : ℂ) * groundQuotient κ ψ σ) =
          ∑ σ, ((torusReference L N σ : ℂ) *
            star (frameEval κ (B L N) σ) * frameEval κ ψ σ) / r := by
              apply Finset.sum_congr rfl
              intro σ hσ
              rw [hLaw σ, groundQuotient]
              dsimp [r]
              push_cast
              have hns : (Complex.normSq (frameEval κ (B L N) σ) : ℂ) =
                  star (frameEval κ (B L N) σ) * frameEval κ (B L N) σ := by
                simpa using Complex.normSq_eq_conj_mul_self
                  (z := frameEval κ (B L N) σ)
              rw [hns]
              field_simp [hGround σ, hnB]
              simp only [starRingEnd_apply]
              ring
      _ = (∑ σ, (torusReference L N σ : ℂ) *
            star (frameEval κ (B L N) σ) * frameEval κ ψ σ) / r := by
              rw [Finset.sum_div]

  have hmean_zero : complexMean (torusLaw L N κ) (groundQuotient κ ψ) = 0 := by
    rw [hmean, hInner (B L N) ψ, hOrth]
    simp

  have hvariance :
      variance (torusLaw L N κ) (groundQuotient κ ψ) =
        weightedNorm (torusReference L N) (frameEval κ ψ) := by
    unfold variance weightedNorm
    simp_rw [hmean_zero, sub_zero]
    apply Finset.sum_congr rfl
    intro σ hσ
    rw [hLaw σ, groundQuotient]
    rw [Complex.normSq_div, Complex.normSq_mul, Complex.normSq_ofReal]
    have hns : Complex.normSq (frameEval κ (B L N) σ) ≠ 0 := by
      intro hz
      exact hGround σ (Complex.normSq_eq_zero.mp hz)
    field_simp [hns, hnB]

  have hnorm : weightedNorm (torusReference L N) (frameEval κ ψ) = ‖ψ‖^2 := by
    rw [weightedNorm_eq_re_weightedInner]
    rw [hInner ψ ψ, inner_self_eq_norm_sq_to_K]
    rw [pow_two]
    rw [Complex.mul_re]
    simp
    ring

  exact ⟨hmean_zero, hvariance.trans hnorm⟩

end AKLT.W.Q047
