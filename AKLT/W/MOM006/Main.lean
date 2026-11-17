module
public import AKLT.Blueprint.Mom.NodesMoments

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.MOM006

theorem main : AKLT.Blueprint.Mom.MixedScalarMomentStatement := by
  have hphi : goldenRatio ^ 2 = goldenRatio + 1 := by
    unfold goldenRatio
    have hs : (Real.sqrt 5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    nlinarith [hs]
  have hr2 : icoRadius ^ 2 = goldenRatio + 2 := by
    unfold icoRadius
    apply Real.sq_sqrt
    unfold goldenRatio
    positivity
  have hr4 : icoRadius ^ 4 = 5 * goldenRatio ^ 2 := by
    calc
      icoRadius ^ 4 = (icoRadius ^ 2) ^ 2 := by ring
      _ = (goldenRatio + 2) ^ 2 := by rw [hr2]
      _ = 5 * goldenRatio ^ 2 := by nlinarith [hphi]
  have hphi_pos : 0 < goldenRatio := by
    unfold goldenRatio
    positivity
  have hrpos : 0 < icoRadius := by
    unfold icoRadius
    exact Real.sqrt_pos.2 (by linarith)
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all
  all_goals
    simp [moment, icoVector, signValue, Fintype.sum_prod_type, Fin.sum_univ_succ]
    field_simp [ne_of_gt hrpos]
    rw [hr4]
    nlinarith [hphi]

end AKLT.W.MOM006

#print axioms AKLT.W.MOM006.main
