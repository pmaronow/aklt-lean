import AKLT.Blueprint.Mom.NodesMoments

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.MOM004

private lemma goldenRatio_sq : goldenRatio ^ 2 = goldenRatio + 1 := by
  unfold goldenRatio
  have hs : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [hs]

private lemma goldenRatio_pos : 0 < goldenRatio := by
  unfold goldenRatio
  positivity

private lemma icoRadius_sq : icoRadius ^ 2 = goldenRatio + 2 := by
  unfold icoRadius
  rw [Real.sq_sqrt (by have := goldenRatio_pos; linarith)]

private lemma icoRadius_pos : 0 < icoRadius := by
  unfold icoRadius
  apply Real.sqrt_pos.2
  have := goldenRatio_pos
  linarith

theorem main : AKLT.Blueprint.Mom.SecondScalarMomentStatement := by
  intro i
  fin_cases i <;>
    norm_num [AKLT.Blueprint.Mom.SecondScalarMomentStatement,
      moment, icoVector, signValue, Fintype.sum_prod_type, Fin.sum_univ_succ] <;>
    simp only [div_pow] <;>
    rw [icoRadius_sq] <;>
    simp only [goldenRatio_sq] <;>
    field_simp [ne_of_gt (show 0 < goldenRatio + 2 by have := goldenRatio_pos; linarith)] <;>
    nlinarith [goldenRatio_sq]

end AKLT.W.MOM004
