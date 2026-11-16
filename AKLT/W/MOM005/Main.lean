import AKLT.Blueprint.Mom.NodesMoments

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Mom

namespace AKLT.W.MOM005

private lemma goldenRatio_sq : goldenRatio ^ 2 = goldenRatio + 1 := by
  unfold goldenRatio
  have hs : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith

private lemma icoRadius_sq : icoRadius ^ 2 = goldenRatio + 2 := by
  unfold icoRadius
  have hp : 0 ≤ goldenRatio + 2 := by
    unfold goldenRatio
    positivity
  exact Real.sq_sqrt hp

private lemma icoRadius_fourth : icoRadius ^ 4 = 5 * goldenRatio ^ 2 := by
  calc
    icoRadius ^ 4 = (icoRadius ^ 2) ^ 2 := by ring
    _ = (goldenRatio + 2) ^ 2 := by rw [icoRadius_sq]
    _ = 5 * goldenRatio ^ 2 := by nlinarith [goldenRatio_sq]

private lemma one_add_goldenRatio_fourth : 1 + goldenRatio ^ 4 = 3 * goldenRatio ^ 2 := by
  nlinarith [goldenRatio_sq]

theorem main : AKLT.Blueprint.Mom.FourthScalarMomentStatement := by
  intro i
  fin_cases i
  all_goals
    simp [moment, icoVector, signValue, Fintype.sum_prod_type,
      Fin.sum_univ_three, Fin.sum_univ_two]
    have hr : icoRadius ≠ 0 := by
      unfold icoRadius
      exact ne_of_gt (Real.sqrt_pos.2 (by unfold goldenRatio; positivity))
    field_simp [hr]
    nlinarith [one_add_goldenRatio_fourth, icoRadius_fourth]

end AKLT.W.MOM005
