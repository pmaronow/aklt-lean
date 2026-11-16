import AKLT.Blueprint.Rec.NodesResponse

noncomputable section

open AKLT.Defs

namespace AKLT.W.REC007

private theorem logarithmicMean_swap (x y : ℝ) :
    logarithmicMean x y = logarithmicMean y x := by
  by_cases h : x = y
  · subst y
    rfl
  · have hyx : y ≠ x := Ne.symm h
    unfold logarithmicMean
    rw [ite_eq_right h, ite_eq_right hyx]
    have hnum : x - y = -(y - x) := by ring
    have hden : Real.log x - Real.log y = -(Real.log y - Real.log x) := by ring
    simp only [hnum, hden, neg_div_neg_eq]

private theorem logarithmicMean_lt_bounds {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hxy : x < y) :
    0 < logarithmicMean x y ∧ x ≤ logarithmicMean x y ∧
      logarithmicMean x y ≤ y := by
  have hlog : Real.log x < Real.log y := Real.log_lt_log hx hxy
  have hden : 0 < Real.log y - Real.log x := by linarith
  have hform : logarithmicMean x y = (y - x) / (Real.log y - Real.log x) := by
    unfold logarithmicMean
    rw [ite_eq_right (ne_of_lt hxy)]
    have hnum : x - y = -(y - x) := by ring
    have hden' : Real.log x - Real.log y = -(Real.log y - Real.log x) := by ring
    simp only [hnum, hden', neg_div_neg_eq]
  have hlogUpper := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rw [Real.log_div hy.ne' hx.ne'] at hlogUpper
  have hmulLower : x * (Real.log y - Real.log x) ≤ y - x := by
    have h := mul_le_mul_of_nonneg_left hlogUpper hx.le
    have hsimp : x * (y / x - 1) = y - x := by field_simp
    rw [hsimp] at h
    exact h
  have hlogLower := Real.one_sub_inv_le_log_of_pos (div_pos hy hx)
  rw [Real.log_div hy.ne' hx.ne'] at hlogLower
  have hratio : 1 - (y / x)⁻¹ = (y - x) / y := by field_simp
  rw [hratio] at hlogLower
  have hmulUpper : y - x ≤ y * (Real.log y - Real.log x) := by
    have h := mul_le_mul_of_nonneg_left hlogLower hy.le
    have hsimp : y * ((y - x) / y) = y - x := by field_simp
    rw [hsimp] at h
    exact h
  rw [hform]
  refine ⟨div_pos (sub_pos.mpr hxy) hden, ?_, ?_⟩
  · exact (le_div_iff₀ hden).2 hmulLower
  · exact (div_le_iff₀ hden).2 hmulUpper

private theorem logarithmicMean_divided_difference {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    Real.log x - Real.log y = (x - y) / logarithmicMean x y := by
  have hlog : Real.log x ≠ Real.log y := by
    intro heq
    rcases lt_trichotomy x y with hlt | heqxy | hgt
    · exact (ne_of_lt (Real.log_lt_log hx hlt)) heq
    · exact hxy heqxy
    · exact (ne_of_gt (Real.log_lt_log hy hgt)) heq
  unfold logarithmicMean
  rw [ite_eq_right hxy]
  field_simp

theorem main : AKLT.Blueprint.Rec.LogMeanBasicStatement := by
  intro x y hx hy
  by_cases hxy : x = y
  · subst y
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [logarithmicMean] using hx
    · simp [logarithmicMean]
    · simp [logarithmicMean]
    · simp [logarithmicMean]
  · rcases lt_or_gt_of_ne hxy with hlt | hgt
    · obtain ⟨hpos, hlo, hhi⟩ := logarithmicMean_lt_bounds hx hy hlt
      refine ⟨hpos, ?_, ?_, logarithmicMean_divided_difference hx hy hxy⟩
      · simpa [min_eq_left (le_of_lt hlt)] using hlo
      · simpa [max_eq_right (le_of_lt hlt)] using hhi
    · have hswap := logarithmicMean_lt_bounds hy hx hgt
      rw [logarithmicMean_swap] at hswap
      obtain ⟨hpos, hlo, hhi⟩ := hswap
      refine ⟨hpos, ?_, ?_, logarithmicMean_divided_difference hx hy hxy⟩
      · simpa [min_eq_right (le_of_lt hgt)] using hlo
      · simpa [max_eq_left (le_of_lt hgt)] using hhi

end AKLT.W.REC007
