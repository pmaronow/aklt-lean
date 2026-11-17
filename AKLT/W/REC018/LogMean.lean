module
public import AKLT.Blueprint.Rec.NodesResponse

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped Interval
open AKLT.Defs

namespace AKLT.W.REC018

/-- An integral formula that also handles coincident endpoints. -/
theorem logMean_integral (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    logarithmicMean x y =
      ∫ t : ℝ in (0 : ℝ)..1, Real.exp (t * (Real.log x - Real.log y) + Real.log y) := by
  by_cases h : x = y
  · subst y
    simp [logarithmicMean, Real.exp_log hx]
  · have hl : Real.log x - Real.log y ≠ 0 := by
      intro he
      apply h
      exact Real.log_injOn_pos hx hy (sub_eq_zero.mp he)
    have hd (t : ℝ) : HasDerivAt
        (fun s : ℝ => Real.exp (s * (Real.log x - Real.log y) + Real.log y) /
          (Real.log x - Real.log y))
        (Real.exp (t * (Real.log x - Real.log y) + Real.log y)) t := by
      convert ((((hasDerivAt_id t).mul_const (Real.log x - Real.log y)).add_const
        (Real.log y)).exp.div_const (Real.log x - Real.log y)) using 1 <;>
        simp [mul_comm, hl]
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : ℝ)) (b := 1) (fun t _ => hd t)
      ((show Continuous (fun t : ℝ => Real.exp
        (t * (Real.log x - Real.log y) + Real.log y)) by fun_prop).intervalIntegrable _ _)
    rw [hi]
    simp [logarithmicMean, h, Real.exp_log hx, Real.exp_log hy, sub_div]

theorem logMean_pos (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    0 < logarithmicMean x y := by
  rw [logMean_integral x y hx hy]
  apply intervalIntegral.integral_pos (by norm_num)
  · fun_prop
  · intro t _; exact (Real.exp_pos _).le
  · exact ⟨0, by simp, Real.exp_pos _⟩

/-- Strictness in the second coordinate survives a weak inequality in the first. -/
theorem logMean_strict_compare (x x' y y' : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hxx : x ≤ x') (hyy : y < y') :
    logarithmicMean x y < logarithmicMean x' y' := by
  have hx' : 0 < x' := hx.trans_le hxx
  have hy' : 0 < y' := hy.trans hyy
  rw [logMean_integral x y hx hy, logMean_integral x' y' hx' hy']
  apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (by norm_num)
  · fun_prop
  · fun_prop
  · intro t ht
    apply Real.exp_le_exp.mpr
    have hxlog := Real.log_le_log hx hxx
    have hylog := (Real.log_lt_log hy hyy).le
    have h1 := mul_le_mul_of_nonneg_left hxlog ht.1.le
    have h2 := mul_le_mul_of_nonneg_left hylog (show 0 ≤ 1 - t by linarith [ht.2])
    nlinarith
  · refine ⟨0, by simp, ?_⟩
    simpa [Real.exp_log hy, Real.exp_log hy'] using hyy

theorem logMean_scale (c x y : ℝ) (hc : 0 < c) (hx : 0 < x) (hy : 0 < y) :
    logarithmicMean (c * x) (c * y) = c * logarithmicMean x y := by
  by_cases h : x = y
  · subst y; simp [logarithmicMean]
  · have h' : c * x ≠ c * y := fun he => h (mul_left_cancel₀ hc.ne' he)
    simp only [logarithmicMean, ite_eq_right h, ite_eq_right h',
      Real.log_mul hc.ne' hx.ne', Real.log_mul hc.ne' hy.ne']
    rw [show Real.log c + Real.log x - (Real.log c + Real.log y) =
      Real.log x - Real.log y by ring]
    ring

theorem alpha_of_comparison (It I₀ Jt J₀ : ℝ)
    (hIt : 0 < It) (hI₀ : 0 < I₀) (hJt : 0 < Jt) (hJ₀ : 0 < J₀)
    (ht : 3 * It ≤ 5 * Jt) (h₀ : 3 * I₀ < 5 * J₀) :
    0 < 1 / (3 * logarithmicMean It I₀) - 1 / (5 * logarithmicMean Jt J₀) := by
  have h := logMean_strict_compare (3 * It) (5 * Jt) (3 * I₀) (5 * J₀)
    (by positivity) (by positivity) ht h₀
  rw [logMean_scale 3 It I₀ (by norm_num) hIt hI₀,
    logMean_scale 5 Jt J₀ (by norm_num) hJt hJ₀] at h
  have hpos : 0 < 3 * logarithmicMean It I₀ :=
    mul_pos (by norm_num) (logMean_pos It I₀ hIt hI₀)
  exact sub_pos.mpr (one_div_lt_one_div_of_lt hpos h)

end AKLT.W.REC018
