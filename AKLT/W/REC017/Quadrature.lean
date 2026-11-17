module
public import AKLT.Blueprint.Rec.NodesResponse

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC017

theorem radius_pos : 0 < icoRadius := by
  unfold icoRadius goldenRatio
  positivity

theorem golden_sq : goldenRatio ^ 2 = goldenRatio + 1 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  unfold goldenRatio
  nlinarith

theorem radius_sq : icoRadius ^ 2 = 1 + goldenRatio ^ 2 := by
  rw [icoRadius, Real.sq_sqrt (by unfold goldenRatio; positivity), golden_sq]
  ring

theorem ico_unit (j : IcoLetter) : normSq (icoVector j) = 1 := by
  rcases j with ⟨a, b, c⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [normSq, dot, Fin.sum_univ_succ, icoVector, signValue] <;>
    field_simp [ne_of_gt radius_pos] <;> nlinarith [radius_sq]

theorem spin_ball (j : SpinLetter) : normSq (spinVector j) ≤ 1 := by
  cases j with
  | none => norm_num [spinVector, normSq, dot]
  | some j => exact (ico_unit j).le

theorem dot_comm (a b : Vec3) : dot a b = dot b a := by
  unfold dot
  congr 1
  funext i
  ring

theorem dot_bounds {a b : Vec3} (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) :
    -1 ≤ dot a b ∧ dot a b ≤ 1 := by
  have hp : 0 ≤ ∑ i : Fin 3, (a i + b i) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hm : 0 ≤ ∑ i : Fin 3, (a i - b i) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have ep : (∑ i : Fin 3, (a i + b i) ^ 2) = normSq a + 2 * dot a b + normSq b := by
    simp [normSq, dot, Fin.sum_univ_succ]
    ring
  have em : (∑ i : Fin 3, (a i - b i) ^ 2) = normSq a - 2 * dot a b + normSq b := by
    simp [normSq, dot, Fin.sum_univ_succ]
    ring
  rw [ep] at hp
  rw [em] at hm
  constructor <;> linarith

theorem weight_nonneg (s : Status) (j : SpinLetter) : 0 ≤ spinWeight s j := by
  cases s <;> cases j <;> norm_num [spinWeight]

theorem site_U_pair (a b : Vec3) :
    siteFunctional .U (fun v => (1 + dot v a) * (1 + dot v b)) =
      1 + dot a b / 3 := by
  simp [siteFunctional, Fintype.sum_option, Fintype.sum_prod_type,
    Fin.sum_univ_succ, spinWeight, spinVector, icoVector, signValue, dot]
  field_simp [ne_of_gt radius_pos]
  linear_combination -12 * (a 0 * b 0 + a 1 * b 1 + a 2 * b 2) * radius_sq

theorem site_D_single (a : Vec3) :
    siteFunctional .D (fun v => 1 + dot v a) = 1 := by
  simp [siteFunctional, Fintype.sum_option, Fintype.sum_prod_type,
    Fin.sum_univ_succ, spinWeight, spinVector, icoVector, signValue, dot]
  ring

end AKLT.W.REC017
