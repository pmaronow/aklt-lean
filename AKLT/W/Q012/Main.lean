module
public import AKLT.Blueprint.Q.NodesTight

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Challenge AKLT.Blueprint.Q

namespace AKLT.W.Q012

private theorem goldenRatio_sq : goldenRatio ^ 2 = goldenRatio + 1 := by
  unfold goldenRatio
  have hs : (Real.sqrt 5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith

private theorem icoRadius_sq : icoRadius ^ 2 = goldenRatio + 2 := by
  unfold icoRadius
  rw [Real.sq_sqrt (by unfold goldenRatio; positivity)]

private theorem goldenRatio_fourth : goldenRatio ^ 4 + 1 = 3 * goldenRatio ^ 2 := by
  nlinarith [goldenRatio_sq]

private theorem goldenRatio_fourth_sub : goldenRatio ^ 4 = 3 * goldenRatio ^ 2 - 1 := by
  linarith [goldenRatio_fourth]

private theorem goldenRatio_fourth_sub_complex :
    (goldenRatio : ℂ) ^ 4 = 3 * (goldenRatio : ℂ) ^ 2 - 1 := by
  exact_mod_cast goldenRatio_fourth_sub

set_option maxHeartbeats 1000000 in
theorem main : AKLT.Blueprint.Q.QuarticOffDiagonalStatement := by
  intro j k hjk
  have hφ4 := goldenRatio_fourth_sub_complex
  fin_cases j <;> fin_cases k <;>
    simp_all [complexMoment, quarticKernel, icoVector, signValue,
      Fintype.sum_prod_type, Fin.sum_univ_succ] <;> try ring
  all_goals
    simp [Complex.I_sq, Complex.I_pow_four, hφ4] <;> ring

end AKLT.W.Q012
