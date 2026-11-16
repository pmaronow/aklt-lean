import AKLT.Blueprint.Rec.NodesResponse

noncomputable section

open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC019

/-- The exponential integral includes the diagonal case of the logarithmic mean. -/
theorem logMean_integral {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    logarithmicMean x y = ∫ t : ℝ in 0..1,
      Real.exp (t * Real.log x + (1 - t) * Real.log y) := by
  by_cases hxy : x = y
  · subst y
    simp only [logarithmicMean]
    have he : (fun t : ℝ => Real.exp (t * Real.log x + (1 - t) * Real.log x)) =
        fun _ => x := by
      funext t
      rw [show t * Real.log x + (1 - t) * Real.log x = Real.log x by ring,
        Real.exp_log hx]
    rw [he]
    simp
  · have hl : Real.log x - Real.log y ≠ 0 := by
      intro h
      exact hxy (Real.log_injOn_pos hx hy (sub_eq_zero.mp h))
    have he : (fun t : ℝ => Real.exp (t * Real.log x + (1 - t) * Real.log y)) =
        fun t => Real.exp ((Real.log x - Real.log y) * t + Real.log y) := by
      funext t
      congr 1
      ring
    rw [he, intervalIntegral.integral_comp_mul_add _ hl,
      integral_exp]
    simp only [mul_zero, zero_add, mul_one, sub_add_cancel, Real.exp_log hx,
      Real.exp_log hy, smul_eq_mul, logarithmicMean, ite_eq_right hxy]
    ring

theorem logMean_positive {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 < logarithmicMean x y := by
  rw [logMean_integral hx hy]
  apply intervalIntegral.integral_pos (by norm_num)
  · fun_prop
  · intro t ht
    exact (Real.exp_pos _).le
  · exact ⟨0, by norm_num, Real.exp_pos _⟩

theorem logMean_monotone {x x' y y' : ℝ}
    (hx : 0 < x) (hxx : x ≤ x') (hy : 0 < y) (hyy : y ≤ y') :
    logarithmicMean x y ≤ logarithmicMean x' y' := by
  rw [logMean_integral hx hy, logMean_integral (hx.trans_le hxx) (hy.trans_le hyy)]
  apply intervalIntegral.integral_mono_on (by norm_num)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
  intro t ht
  apply Real.exp_le_exp.mpr
  exact add_le_add
    (mul_le_mul_of_nonneg_left (Real.log_le_log hx hxx) ht.1)
    (mul_le_mul_of_nonneg_left (Real.log_le_log hy hyy) (sub_nonneg.mpr ht.2))

theorem logMean_le_upper {x y u : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxu : x ≤ u) (hyu : y ≤ u) : logarithmicMean x y ≤ u := by
  simpa [logarithmicMean] using logMean_monotone hx hxu hy hyu

theorem lower_le_logMean {x y l : ℝ} (hl : 0 < l) (hlx : l ≤ x) (hly : l ≤ y) :
    l ≤ logarithmicMean x y := by
  simpa [logarithmicMean] using logMean_monotone hl hlx hl hly

/-- A rational logarithm bound from the odd series with a geometric remainder. -/
theorem reciprocal_logMean_41_50 :
    1 / (3 * logarithmicMean (41 / 50) 1) ≤ (367502 / 1000000 : ℝ) := by
  have hb := Real.log_div_le_sum_range_add
    (by norm_num : (0 : ℝ) ≤ 9 / 91) (by norm_num : (9 / 91 : ℝ) < 1) 4
  norm_num [Finset.sum_range_succ] at hb
  have hl : Real.log (41 / 50 : ℝ) = -Real.log (50 / 41 : ℝ) := by
    rw [← Real.log_inv]
    norm_num
  norm_num [logarithmicMean, hl] at ⊢
  nlinarith [hb]

end AKLT.W.REC019
