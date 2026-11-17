module
public import AKLT.W.REC005.Free

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

set_option maxHeartbeats 800000
set_option maxRecDepth 2000

namespace AKLT.W.REC005

lemma golden_sq : goldenRatio ^ 2 = goldenRatio + 1 := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  unfold goldenRatio
  nlinarith

lemma radius_sq : icoRadius ^ 2 = goldenRatio + 2 := by
  exact Real.sq_sqrt (by linarith [golden_pos])

lemma radius_four : icoRadius ^ 4 = 5 * goldenRatio ^ 2 := by
  nlinarith [radius_sq, golden_sq, sq_nonneg (icoRadius ^ 2 - (goldenRatio + 2))]

lemma ico_unit (j : IcoLetter) : normSq (icoVector j) = 1 := by
  rcases j with ⟨a, b, c⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [normSq, dot, Fin.sum_univ_three, icoVector, signValue, div_pow] <;>
    field_simp [ne_of_gt radius_pos] <;> nlinarith [golden_sq, radius_sq]

lemma normSq_nonneg (v : Vec3) : 0 ≤ normSq v := by
  change 0 ≤ ∑ i, v i * v i
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))

lemma dot_sq_le (v w : Vec3) : dot v w ^ 2 ≤ normSq v * normSq w := by
  simpa only [dot, normSq, pow_two] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v w

lemma dot_unit_bounds (v w : Vec3) (hv : normSq v = 1) (hw : normSq w = 1) :
    -1 ≤ dot v w ∧ dot v w ≤ 1 := by
  have h := dot_sq_le v w
  rw [hv, hw] at h
  constructor <;> nlinarith

lemma moment_second (i j : Fin 3) :
    moment (fun v => v i * v j) = if i = j then 1 / 3 else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [moment, Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two,
      icoVector, signValue] <;>
    field_simp [ne_of_gt radius_pos] <;> nlinarith [golden_sq, radius_sq]

lemma moment_first (i : Fin 3) : moment (fun v => v i) = 0 := by
  fin_cases i <;>
    simp [moment, Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two,
      icoVector, signValue] <;> ring

lemma moment_third (i j k : Fin 3) : moment (fun v => v i * v j * v k) = 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [moment, Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two,
      icoVector, signValue] <;> ring

lemma moment_fourth (i j k l : Fin 3) :
    moment (fun v => v i * v j * v k * v l) =
      ((if i = j ∧ k = l then 1 else 0) + (if i = k ∧ j = l then 1 else 0) +
        (if i = l ∧ j = k then 1 else 0)) / 15 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [moment, Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two,
      icoVector, signValue] <;>
    field_simp [ne_of_gt radius_pos] <;>
    nlinarith [golden_sq, radius_four, sq_nonneg (goldenRatio ^ 2 - (goldenRatio + 1))]

end AKLT.W.REC005
