import AKLT.Blueprint.Q.NodesFrames

noncomputable section

open AKLT.Defs AKLT.Blueprint.Q

namespace AKLT.W.Q003

set_option maxHeartbeats 1000000 in
theorem main : AKLT.Blueprint.Q.IcoDistanceStatement := by
  intro a b hab
  have hs : (Real.sqrt 5 : ℝ) ^ 2 = 5 := by
    exact Real.sq_sqrt (by norm_num)
  have hp : goldenRatio ^ 2 = goldenRatio + 1 := by
    unfold goldenRatio
    nlinarith [hs]
  have hr : icoRadius ^ 2 = goldenRatio + 2 := by
    unfold icoRadius
    exact Real.sq_sqrt (by unfold goldenRatio; positivity)
  have hphi_pos : 0 < goldenRatio := by
    unfold goldenRatio
    have hs0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
    positivity
  have hrpos : 0 < icoRadius := by
    unfold icoRadius
    exact Real.sqrt_pos.2 (by linarith [hphi_pos])
  rcases a with ⟨ai, ax, ay⟩
  rcases b with ⟨bi, bx, bz⟩
  fin_cases ai <;> fin_cases ax <;> fin_cases ay <;>
    fin_cases bi <;> fin_cases bx <;> fin_cases bz <;>
    (simp [icoVector, signValue, normSq, dot, Fin.sum_univ_succ] at hab ⊢ <;>
      field_simp [ne_of_gt hrpos] <;>
      nlinarith [hp, hr, hs])

end AKLT.W.Q003
