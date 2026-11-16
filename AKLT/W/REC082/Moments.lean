import AKLT.W.REC082.Geometry

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC082

theorem goldenRatio_sq : goldenRatio ^ 2 = goldenRatio + 1 := by
  have h : (Real.sqrt 5)^2 = 5 := Real.sq_sqrt (by norm_num)
  dsimp [goldenRatio]
  nlinarith

theorem icoRadius_pos : 0 < icoRadius := by
  unfold icoRadius goldenRatio
  positivity

theorem icoRadius_sq : icoRadius ^ 2 = goldenRatio + 2 := by
  unfold icoRadius
  apply Real.sq_sqrt
  unfold goldenRatio
  positivity

theorem ico_unit (j : IcoLetter) : normSq (icoVector j) = 1 := by
  have hr : icoRadius ≠ 0 := ne_of_gt icoRadius_pos
  have hp := goldenRatio_sq
  have hrad := icoRadius_sq
  rcases j with ⟨a, b, c⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    norm_num [normSq, dot, Fin.sum_univ_succ, icoVector, signValue] <;>
    field_simp <;> nlinarith

theorem spinVector_ball (j : SpinLetter) : normSq (spinVector j) ≤ 1 := by
  cases j with
  | none => norm_num [spinVector, normSq, dot]
  | some j => exact le_of_eq (ico_unit j)

theorem spinWeight_nonneg (s : Status) (j : SpinLetter) : 0 ≤ spinWeight s j := by
  cases s <;> cases j <;> norm_num [spinWeight]

theorem d_norm_moment : siteFunctional .D normSq = 3 / 5 := by
  have hz : normSq 0 = 0 := by simp [normSq, dot]
  norm_num [siteFunctional, Fintype.sum_option, spinWeight, spinVector, ico_unit,
    hz, Fintype.card_prod]

theorem site_mass (s : Status) (hs : s = .U ∨ s = .D) :
    siteFunctional s (fun _ => 1) = 1 := by
  rcases hs with rfl | rfl <;>
    norm_num [siteFunctional, Fintype.sum_option, spinWeight, Fintype.card_prod]

end AKLT.W.REC082
