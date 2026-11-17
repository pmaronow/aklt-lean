module
public import AKLT.Blueprint.Rec.NodesResponse
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section

open AKLT.Defs
open scoped Interval

namespace AKLT.W.REC008

private theorem logarithmicMean_eq_integral (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    logarithmicMean x y =
      ∫ t in (0 : ℝ)..1, Real.exp (t * Real.log x + (1 - t) * Real.log y) := by
  by_cases hxy : x = y
  · subst y
    have hconst : ∀ t : ℝ,
        Real.exp (t * Real.log x + (1 - t) * Real.log x) = x := by
      intro t
      calc
        Real.exp (t * Real.log x + (1 - t) * Real.log x) = Real.exp (Real.log x) := by
          congr 1
          ring
        _ = x := Real.exp_log hx
    simp [logarithmicMean, hconst]
  · have hlog : Real.log x - Real.log y ≠ 0 := by
      intro h
      apply hxy
      exact Real.log_injOn_pos (Set.mem_Ioi.mpr hx) (Set.mem_Ioi.mpr hy)
        (sub_eq_zero.mp h)
    have hexp : ∀ t : ℝ,
        t * Real.log x + (1 - t) * Real.log y =
          (Real.log x - Real.log y) * t + Real.log y := by
      intro t
      ring
    calc
      logarithmicMean x y = (x - y) / (Real.log x - Real.log y) := by
        simp [logarithmicMean, hxy]
      _ = (Real.log x - Real.log y)⁻¹ * (x - y) := by ring
      _ = ∫ t in (0 : ℝ)..1,
          Real.exp (t * Real.log x + (1 - t) * Real.log y) := by
        simp_rw [hexp]
        rw [intervalIntegral.integral_comp_mul_add (f := Real.exp) hlog (Real.log y)]
        rw [integral_exp]
        simp only [smul_eq_mul]
        rw [show (Real.log x - Real.log y) * 0 + Real.log y = Real.log y by ring,
          show (Real.log x - Real.log y) * 1 + Real.log y = Real.log x by ring,
          Real.exp_log hx, Real.exp_log hy]

theorem main : AKLT.Blueprint.Rec.LogMeanMonotoneStatement := by
  intro x x' y y' hx hxx' hy hyy'
  rw [logarithmicMean_eq_integral x y hx hy,
    logarithmicMean_eq_integral x' y' (lt_of_lt_of_le hx hxx')
      (lt_of_lt_of_le hy hyy')]
  refine intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1) (by norm_num) ?_ ?_ ?_
  · exact (by fun_prop : Continuous fun t : ℝ =>
      Real.exp (t * Real.log x + (1 - t) * Real.log y)).intervalIntegrable 0 1
  · exact (by fun_prop : Continuous fun t : ℝ =>
      Real.exp (t * Real.log x' + (1 - t) * Real.log y')).intervalIntegrable 0 1
  · intro t ht
    have ht0 : 0 ≤ t := ht.1
    have ht1 : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    apply Real.exp_le_exp.mpr
    have hlogx : Real.log x ≤ Real.log x' := Real.log_le_log hx hxx'
    have hlogy : Real.log y ≤ Real.log y' := Real.log_le_log hy hyy'
    have hxpart := mul_le_mul_of_nonneg_left hlogx ht0
    have hypart := mul_le_mul_of_nonneg_left hlogy ht1
    exact add_le_add hxpart hypart

end AKLT.W.REC008

end
