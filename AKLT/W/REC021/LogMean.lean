module
public import AKLT.Blueprint.Rec.NodesResponse

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC021

theorem logarithmicMean_pos_local {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 < logarithmicMean x y := by
  by_cases hxy : x = y
  · simpa [logarithmicMean, hxy] using hx
  · rw [logarithmicMean, if_neg hxy]
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · exact div_pos_of_neg_of_neg (sub_neg.mpr hlt)
        (sub_neg.mpr (Real.log_lt_log hx hlt))
    · exact div_pos (sub_pos.mpr hgt) (sub_pos.mpr (Real.log_lt_log hy hgt))

/-- An exponential integral representation, including coincident arguments. -/
theorem logarithmicMean_integral {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    logarithmicMean x y =
      ∫ t : ℝ in 0..1, Real.exp (t * Real.log x + (1 - t) * Real.log y) := by
  by_cases h : x = y
  · subst y
    simp only [logarithmicMean, if_pos rfl]
    have he : (fun t : ℝ => Real.exp (t * Real.log x + (1 - t) * Real.log x)) =
        fun _ => x := by
      funext t
      rw [show t * Real.log x + (1 - t) * Real.log x = Real.log x by ring,
        Real.exp_log hx]
    rw [he]
    simp
  · have hd : Real.log x - Real.log y ≠ 0 := by
      intro hd
      apply h
      exact Real.log_injOn_pos hx hy (sub_eq_zero.mp hd)
    have hderiv (t : ℝ) :
        HasDerivAt
          (fun u => Real.exp (u * Real.log x + (1 - u) * Real.log y) /
            (Real.log x - Real.log y))
          (Real.exp (t * Real.log x + (1 - t) * Real.log y)) t := by
      have hl : HasDerivAt (fun u : ℝ => u * Real.log x + (1 - u) * Real.log y)
          (Real.log x - Real.log y) t := by
        convert (((hasDerivAt_id t).mul_const (Real.log x)).add
          (((hasDerivAt_id t).const_sub 1).mul_const (Real.log y))) using 1 <;>
          (try (funext u; dsimp)) <;> ring
      convert hl.exp.div_const (Real.log x - Real.log y) using 1
      field_simp
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hderiv t)
      (show IntervalIntegrable
        (fun t : ℝ => Real.exp (t * Real.log x + (1 - t) * Real.log y))
          MeasureTheory.volume 0 1 from Continuous.intervalIntegrable (by fun_prop) _ _)
    simpa [logarithmicMean, h, Real.exp_log hx, Real.exp_log hy, sub_div] using hi.symm

theorem logarithmicMean_monotone : AKLT.Blueprint.Rec.LogMeanMonotoneStatement := by
  intro x x' y y' hx hxx hy hyy
  rw [logarithmicMean_integral hx hy,
    logarithmicMean_integral (hx.trans_le hxx) (hy.trans_le hyy)]
  apply intervalIntegral.integral_mono_on (by norm_num)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  intro t ht
  apply Real.exp_le_exp.mpr
  exact add_le_add
    (mul_le_mul_of_nonneg_left (Real.log_le_log hx hxx) ht.1)
    (mul_le_mul_of_nonneg_left (Real.log_le_log hy hyy) (sub_nonneg.mpr ht.2))

/-- The single logarithmic enclosure needed for this leaf. The four-term
atanh estimate in Mathlib is sharper than the paper's two-term enclosure. -/
theorem crudeLogAt41 :
    reciprocalLogMean (41 / 50 : ℝ) ≤
      (AKLT.Blueprint.Rec.crudeLogUpper (41 / 50) : ℝ) := by
  have h := Real.log_div_le_sum_range_add (x := (9 / 91 : ℝ)) (by norm_num)
    (by norm_num) 4
  norm_num [Finset.sum_range_succ] at h
  have hl : Real.log (50 / 41 : ℝ) = -Real.log (41 / 50 : ℝ) := by
    rw [show (50 / 41 : ℝ) = (41 / 50 : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [hl] at h
  norm_num [reciprocalLogMean, logarithmicMean, AKLT.Blueprint.Rec.crudeLogUpper]
  linarith

#print axioms logarithmicMean_pos_local
#print axioms logarithmicMean_integral
#print axioms logarithmicMean_monotone
#print axioms crudeLogAt41

end AKLT.W.REC021
