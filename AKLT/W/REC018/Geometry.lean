module
public import AKLT.Blueprint.Rec.NodesResponse

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC018

theorem dot_symm (u v : Vec3) : dot u v = dot v u := by
  simp only [dot, mul_comm]

theorem normSq_nonneg (v : Vec3) : 0 ≤ normSq v := by
  unfold normSq dot
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

theorem normSq_sub (u v : Vec3) :
    normSq (u - v) = normSq u + normSq v - 2 * dot u v := by
  simp [normSq, dot, Fin.sum_univ_succ]
  ring

theorem normSq_add (u v : Vec3) :
    normSq (u + v) = normSq u + normSq v + 2 * dot u v := by
  simp [normSq, dot, Fin.sum_univ_succ]
  ring

theorem ball_dot (u v : Vec3) (hu : normSq u ≤ 1) (hv : normSq v ≤ 1) :
    -1 ≤ dot u v ∧ dot u v ≤ 1 := by
  have hminus := normSq_nonneg (u - v)
  have hplus := normSq_nonneg (u + v)
  rw [normSq_sub] at hminus
  rw [normSq_add] at hplus
  constructor <;> linarith

theorem triple_dot_lower (u v w : Vec3)
    (hu : normSq u ≤ 1) (hv : normSq v ≤ 1) (hw : normSq w ≤ 1) :
    -(3 / 2 : ℝ) ≤ dot u v + dot u w + dot v w := by
  have heq : normSq (u + v + w) =
      normSq u + normSq v + normSq w + 2 * (dot u v + dot u w + dot v w) := by
    simp [normSq, dot, Fin.sum_univ_succ]
    ring
  have h := normSq_nonneg (u + v + w)
  rw [heq] at h
  linarith

theorem golden_sq : goldenRatio ^ 2 = goldenRatio + 1 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  dsimp [goldenRatio]
  nlinarith

theorem radius_pos : 0 < icoRadius := by
  apply Real.sqrt_pos.2
  dsimp [goldenRatio]
  positivity

theorem radius_sq : icoRadius ^ 2 = goldenRatio + 2 := by
  apply Real.sq_sqrt
  dsimp [goldenRatio]
  positivity

theorem ico_unit (j : IcoLetter) : normSq (icoVector j) = 1 := by
  have hr : icoRadius ≠ 0 := ne_of_gt radius_pos
  have hphi := golden_sq
  have hr2 := radius_sq
  rcases j with ⟨a, b, c⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    norm_num [icoVector, signValue, normSq, dot, Fin.sum_univ_succ] <;>
    field_simp <;> nlinarith

theorem spin_ball (j : SpinLetter) : normSq (spinVector j) ≤ 1 := by
  cases j with
  | none => norm_num [spinVector, normSq, dot]
  | some j => exact (ico_unit j).le

 def baseLetter : IcoLetter := (0, 0, 0)
 def otherLetter : IcoLetter := (0, 1, 0)

theorem base_other_dot :
    0 < 1 + dot (icoVector baseLetter) (icoVector otherLetter) ∧
    dot (icoVector baseLetter) (icoVector otherLetter) < 1 := by
  have hr : icoRadius ≠ 0 := ne_of_gt radius_pos
  have hphi := golden_sq
  have hr2 := radius_sq
  have hp : 0 < goldenRatio := by dsimp [goldenRatio]; positivity
  have heq : dot (icoVector baseLetter) (icoVector otherLetter) =
      goldenRatio / (goldenRatio + 2) := by
    norm_num [baseLetter, otherLetter, icoVector, signValue, dot, Fin.sum_univ_succ]
    field_simp
    nlinarith
  rw [heq]
  constructor
  · have : 0 < goldenRatio / (goldenRatio + 2) := by positivity
    linarith
  · exact (div_lt_one (by positivity)).2 (by linarith)

end AKLT.W.REC018
