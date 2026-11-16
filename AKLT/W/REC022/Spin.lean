import AKLT.Blueprint.Rec.NodesResponse

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC022

theorem golden_sq : goldenRatio ^ 2 = goldenRatio + 1 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  dsimp [goldenRatio]
  nlinarith

theorem radius_sq : icoRadius ^ 2 = goldenRatio + 2 := by
  apply Real.sq_sqrt
  dsimp [goldenRatio]
  positivity

theorem radius_pos : 0 < icoRadius := by
  dsimp [icoRadius, goldenRatio]
  positivity

theorem ico_unit (j : IcoLetter) : normSq (icoVector j) = 1 := by
  rcases j with ⟨i, a, b⟩
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    norm_num [normSq, dot, Fin.sum_univ_three, icoVector, signValue] <;>
    field_simp [ne_of_gt radius_pos] <;> nlinarith [golden_sq, radius_sq]

theorem dot_comm (a b : Vec3) : dot a b = dot b a := by
  simp only [dot, mul_comm]

theorem normSq_nonneg (a : Vec3) : 0 ≤ normSq a := by
  unfold normSq dot
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (a i)

theorem spin_ball (j : SpinLetter) : normSq (spinVector j) ≤ 1 := by
  cases j with
  | none => norm_num [spinVector, normSq, dot]
  | some j => exact (ico_unit j).le

theorem ball_factor (a b : Vec3) (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) :
    0 ≤ 1 + dot a b := by
  have h := normSq_nonneg (a + b)
  have he : normSq (a + b) = normSq a + normSq b + 2 * dot a b := by
    simp only [normSq, dot, Pi.add_apply, Fin.sum_univ_three]
    ring
  rw [he] at h
  linarith

theorem three_scalar_lower (a b c : Vec3)
    (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) (hc : normSq c ≤ 1) :
    (1 / 2 : ℝ) ≤ 1 + (dot a b + dot a c + dot b c) / 3 := by
  have h := normSq_nonneg (a + b + c)
  have he : normSq (a + b + c) = normSq a + normSq b + normSq c +
      2 * (dot a b + dot a c + dot b c) := by
    simp only [normSq, dot, Pi.add_apply, Fin.sum_univ_three]
    ring
  rw [he] at h
  linarith

theorem two_scalar_lower (a b : Vec3) (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) :
    (4 / 5 : ℝ) ≤ 1 + dot a b / 5 := by
  have := ball_factor a b ha hb
  linarith

theorem weight_nonneg (s : Status) (j : SpinLetter) : 0 ≤ spinWeight s j := by
  cases s <;> cases j <;> norm_num [spinWeight]

theorem site_U_three (a b c : Vec3) :
    siteFunctional .U (fun v => (1 + dot v a) * (1 + dot v b) * (1 + dot v c)) =
      1 + (dot a b + dot a c + dot b c) / 3 := by
  have h : siteFunctional .U
      (fun v => (1 + dot v a) * (1 + dot v b) * (1 + dot v c)) =
      1 + (1 + goldenRatio ^ 2) / (3 * icoRadius ^ 2) *
        (dot a b + dot a c + dot b c) := by
    simp [siteFunctional, Fintype.sum_option, spinWeight, spinVector,
      Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two, icoVector,
      signValue, dot]
    ring
  rw [h]
  have he : 1 + goldenRatio ^ 2 = icoRadius ^ 2 := by
    linarith [golden_sq, radius_sq]
  rw [he]
  field_simp [ne_of_gt radius_pos]

theorem site_D_two (a b : Vec3) :
    siteFunctional .D (fun v => (1 + dot v a) * (1 + dot v b)) =
      1 + dot a b / 5 := by
  have h : siteFunctional .D (fun v => (1 + dot v a) * (1 + dot v b)) =
      1 + (1 + goldenRatio ^ 2) / (5 * icoRadius ^ 2) * dot a b := by
    simp [siteFunctional, Fintype.sum_option, spinWeight, spinVector,
      Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two, icoVector,
      signValue, dot]
    ring
  rw [h]
  have he : 1 + goldenRatio ^ 2 = icoRadius ^ 2 := by
    linarith [golden_sq, radius_sq]
  rw [he]
  field_simp [ne_of_gt radius_pos]

theorem logMean_identity (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    0 < logarithmicMean x y ∧
      Real.log x - Real.log y = (x - y) / logarithmicMean x y := by
  by_cases he : x = y
  · subst y
    simp [logarithmicMean, hx]
  · have hl : Real.log x - Real.log y ≠ 0 := by
      intro h
      exact he (Real.log_injOn_pos hx hy (sub_eq_zero.mp h))
    have hp : 0 < (x - y) / (Real.log x - Real.log y) := by
      rcases lt_or_gt_of_ne he with hxy | hyx
      · exact div_pos_of_neg_of_neg (sub_neg.mpr hxy)
          (sub_neg.mpr (Real.strictMonoOn_log hx hy hxy))
      · exact div_pos (sub_pos.mpr hyx)
          (sub_pos.mpr (Real.strictMonoOn_log hy hx hyx))
    simp only [logarithmicMean, ite_eq_right he]
    refine ⟨hp, ?_⟩
    field_simp

end AKLT.W.REC022
