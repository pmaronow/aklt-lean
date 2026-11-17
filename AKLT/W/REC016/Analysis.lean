module
public import AKLT.Blueprint.Rec.NodesResponse

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC016

theorem affine_pos {x y t : ℝ} (hx : 0 < x) (hy : 0 < y)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : 0 < (1 - t) * x + t * y := by
  by_cases h : t = 1
  · simp [h, hy]
  · have ht1 : t < 1 := ht.2.lt_or_eq.resolve_right h
    exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr ht1) hx)
      (mul_nonneg ht.1 hy.le)

theorem inv_affine_continuous {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    ContinuousOn (fun t : ℝ => ((1 - t) * x + t * y)⁻¹) (Set.Icc 0 1) := by
  apply ContinuousOn.inv₀ (by fun_prop)
  intro t ht
  exact (affine_pos hx hy ht).ne'

theorem reciprocal_integral {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (logarithmicMean x y)⁻¹ =
      ∫ t in (0 : ℝ)..1, ((1 - t) * x + t * y)⁻¹ := by
  by_cases hxy : x = y
  · subst y
    simp only [logarithmicMean, ite_self]
    have h : (fun t : ℝ => ((1 - t) * x + t * x)⁻¹) = fun _ => x⁻¹ := by
      funext t
      congr 1
      ring
    rw [h]
    simp
  · have hdiff : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
    have h : (fun t : ℝ => ((1 - t) * x + t * y)⁻¹) =
        fun t => ((y - x) * t + x)⁻¹ := by
      funext t
      congr 1
      ring
    rw [h, intervalIntegral.integral_comp_mul_add _ hdiff]
    simp only [mul_zero, zero_add, mul_one, sub_add_cancel,
      integral_inv_of_pos hx hy, smul_eq_mul]
    rw [logarithmicMean, if_neg hxy, inv_div, Real.log_div hy.ne' hx.ne']
    field_simp
    <;> ring

theorem logarithmicMean_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 < logarithmicMean x y := by
  unfold logarithmicMean
  split_ifs with h
  · exact hx
  · rcases lt_or_gt_of_ne h with hlt | hgt
    · exact div_pos_of_neg_of_neg (sub_neg.mpr hlt)
        (sub_neg.mpr (Real.log_lt_log hx hlt))
    · exact div_pos (sub_pos.mpr hgt) (sub_pos.mpr (Real.log_lt_log hy hgt))

theorem reciprocal_antitone {x x' y y' : ℝ}
    (hx : 0 < x) (hxx : x ≤ x') (hy : 0 < y) (hyy : y ≤ y') :
    (logarithmicMean x' y')⁻¹ ≤ (logarithmicMean x y)⁻¹ := by
  rw [reciprocal_integral (hx.trans_le hxx) (hy.trans_le hyy), reciprocal_integral hx hy]
  apply intervalIntegral.integral_mono_on (by norm_num)
    ((inv_affine_continuous (hx.trans_le hxx) (hy.trans_le hyy)).intervalIntegrable_of_Icc
      (by norm_num))
    ((inv_affine_continuous hx hy).intervalIntegrable_of_Icc (by norm_num))
  intro t ht
  apply inv_anti₀ (affine_pos hx hy ht)
  exact add_le_add (mul_le_mul_of_nonneg_left hxx (by linarith [ht.2]))
    (mul_le_mul_of_nonneg_left hyy ht.1)

theorem logarithmicMean_mono : AKLT.Blueprint.Rec.LogMeanMonotoneStatement := by
  intro x x' y y' hx hxx hy hyy
  exact (inv_le_inv₀ (logarithmicMean_pos (hx.trans_le hxx) (hy.trans_le hyy))
    (logarithmicMean_pos hx hy)).mp (reciprocal_antitone hx hxx hy hyy)

/-- The standard two-term log-series remainder already suffices for this row. -/
theorem base_coefficient_bound :
    (logarithmicMean (22 / 25 : ℝ) 1)⁻¹ / 3 ≤ 35510 / 100000 := by
  have h := Real.log_div_le_sum_range_add (x := (3 / 47 : ℝ)) (by norm_num)
    (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  have hlog : -Real.log (22 / 25 : ℝ) ≤ (4866481 / 38068425 : ℝ) := by
    rw [show (25 / 22 : ℝ) = (22 / 25 : ℝ)⁻¹ by norm_num, Real.log_inv] at h
    linarith
  norm_num [logarithmicMean, Real.log_one] at *
  linarith

theorem coefficient_bound_of_intervals {x y : ℝ}
    (hx : (22 / 25 : ℝ) ≤ x) (hy : 1 ≤ y) :
    1 / (3 * logarithmicMean x y) ≤ 35510 / 100000 := by
  have h := reciprocal_antitone (x := (22 / 25 : ℝ)) (x' := x)
    (y := 1) (y' := y) (by norm_num) hx (by norm_num) hy
  calc
    1 / (3 * logarithmicMean x y) = (logarithmicMean x y)⁻¹ / 3 := by
      simp [div_eq_mul_inv, mul_comm]
    _ ≤ (logarithmicMean (22 / 25 : ℝ) 1)⁻¹ / 3 := by linarith
    _ ≤ _ := base_coefficient_bound

#print axioms reciprocal_integral
#print axioms logarithmicMean_mono
#print axioms base_coefficient_bound
#print axioms coefficient_bound_of_intervals

end AKLT.W.REC016
