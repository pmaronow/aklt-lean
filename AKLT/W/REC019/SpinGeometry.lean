import AKLT.Blueprint.Rec.NodesResponse

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC019

theorem goldenRatio_positive : 0 < goldenRatio := by
  unfold goldenRatio
  positivity

theorem goldenRatio_square : goldenRatio ^ 2 = goldenRatio + 1 := by
  have h : (Real.sqrt 5) ^ 2 = (5 : ℝ) := Real.sq_sqrt (by norm_num)
  unfold goldenRatio
  nlinarith

theorem icoRadius_positive : 0 < icoRadius := by
  exact Real.sqrt_pos.mpr (by linarith [goldenRatio_positive])

theorem icoRadius_square : icoRadius ^ 2 = goldenRatio + 2 := by
  exact Real.sq_sqrt (by linarith [goldenRatio_positive])

theorem icoVector_unit (j : IcoLetter) : normSq (icoVector j) = 1 := by
  have hr := icoRadius_square
  have hp := goldenRatio_square
  have hn := ne_of_gt icoRadius_positive
  rcases j with ⟨k, a, b⟩
  fin_cases k <;> fin_cases a <;> fin_cases b <;>
    simp [normSq, dot, Fin.sum_univ_three, icoVector, signValue] <;>
    field_simp <;> nlinarith

theorem spinVector_ball (j : SpinLetter) : normSq (spinVector j) ≤ 1 := by
  cases j with
  | none => simp [spinVector, normSq, dot]
  | some j => exact (icoVector_unit j).le

theorem normSq_nonnegative (a : Vec3) : 0 ≤ normSq a := by
  unfold normSq dot
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (a i)

theorem dot_square_le (a b : Vec3) : dot a b ^ 2 ≤ normSq a * normSq b := by
  simpa [dot, normSq, pow_two] using
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b)

theorem dot_ball_bounds {a b : Vec3} (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) :
    -1 ≤ dot a b ∧ dot a b ≤ 1 := by
  have h := dot_square_le a b
  have hn := normSq_nonnegative a
  have hm := normSq_nonnegative b
  have hc : normSq a * normSq b ≤ 1 := by nlinarith
  constructor <;> nlinarith [sq_nonneg (dot a b + 1), sq_nonneg (dot a b - 1)]

theorem spinWeight_nonnegative (s : Status) (j : SpinLetter) : 0 ≤ spinWeight s j := by
  cases s <;> cases j <;> norm_num [spinWeight]

theorem sum_three_dot_lower {a b c : Vec3} (ha : normSq a ≤ 9 / 25)
    (hb : normSq b ≤ 9 / 25) (hc : normSq c ≤ 9 / 25) :
    -(27 / 50 : ℝ) ≤ dot a b + dot a c + dot b c := by
  have he : normSq (a + b + c) = normSq a + normSq b + normSq c +
      2 * (dot a b + dot a c + dot b c) := by
    simp [normSq, dot, Fin.sum_univ_three]
    ring
  have hn := normSq_nonnegative (a + b + c)
  linarith

theorem dot_small_ball_bounds {a b : Vec3}
    (ha : normSq a ≤ 9 / 25) (hb : normSq b ≤ 9 / 25) :
    -(9 / 25 : ℝ) ≤ dot a b ∧ dot a b ≤ 9 / 25 := by
  have h := dot_square_le a b
  have hn := normSq_nonnegative a
  have hm := normSq_nonnegative b
  have hc : normSq a * normSq b ≤ (9 / 25 : ℝ)^2 := by nlinarith
  constructor <;> nlinarith [sq_nonneg (dot a b + 9 / 25),
    sq_nonneg (dot a b - 9 / 25)]

end AKLT.W.REC019
