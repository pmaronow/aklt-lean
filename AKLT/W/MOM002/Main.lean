module
public import AKLT.Blueprint.Mom.NodesMoments

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open AKLT.Defs

namespace AKLT.W.MOM002

lemma goldenRatio_sq : goldenRatio ^ 2 = goldenRatio + 1 := by
  unfold goldenRatio
  have hs : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith

lemma icoRadius_pos : 0 < icoRadius := by
  unfold icoRadius goldenRatio
  positivity

lemma icoRadius_sq : icoRadius ^ 2 = goldenRatio + 2 := by
  unfold icoRadius
  apply Real.sq_sqrt
  unfold goldenRatio
  positivity

theorem main : AKLT.Blueprint.Mom.IcoUnitStatement := by
  intro j
  rcases j with ⟨a, b, c⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [normSq, dot, icoVector, signValue, Fin.sum_univ_succ] <;>
    field_simp [ne_of_gt icoRadius_pos] <;>
    rw [icoRadius_sq, goldenRatio_sq] <;> ring

end AKLT.W.MOM002
