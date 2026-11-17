module
public import AKLT.Blueprint.Rec.NodesResponse

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC021

theorem golden_pos : 0 < goldenRatio := by
  unfold goldenRatio
  positivity

theorem golden_sq : goldenRatio ^ 2 = goldenRatio + 1 := by
  unfold goldenRatio
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]

theorem golden_cube : goldenRatio ^ 3 = 2 * goldenRatio + 1 := by
  nlinarith [golden_sq, mul_nonneg golden_pos.le (sq_nonneg (goldenRatio - 1))]

theorem golden_fourth : goldenRatio ^ 4 = 3 * goldenRatio + 2 := by
  nlinarith [golden_sq, sq_nonneg (goldenRatio ^ 2 - (goldenRatio + 1))]

theorem radius_pos : 0 < icoRadius := by
  exact Real.sqrt_pos.mpr (by linarith [golden_pos])

theorem radius_sq : icoRadius ^ 2 = goldenRatio + 2 := by
  exact Real.sq_sqrt (by linarith [golden_pos])

theorem radius_fourth : icoRadius ^ 4 = 5 * goldenRatio + 5 := by
  nlinarith [radius_sq, golden_sq, sq_nonneg (icoRadius ^ 2 - (goldenRatio + 2))]

theorem ico_unit (j : IcoLetter) : normSq (icoVector j) = 1 := by
  rcases j with ⟨i, a, b⟩
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    norm_num [normSq, dot, icoVector, signValue, Fin.sum_univ_three] <;>
    field_simp [ne_of_gt radius_pos] <;> nlinarith [radius_sq, golden_sq]

theorem spin_norm (j : SpinLetter) : normSq (spinVector j) = 0 ∨
    normSq (spinVector j) = 1 := by
  cases j with
  | none => left; simp [normSq, dot, spinVector]
  | some j => right; exact ico_unit j

/-- The degree-three local normalizer, computed on the actual twelve atoms. -/
theorem site_cubic_U (a b c : Vec3) :
    siteFunctional .U (fun n => (1 + dot n a) * (1 + dot n b) * (1 + dot n c)) =
      1 + (dot a b + dot a c + dot b c) / 3 := by
  norm_num [siteFunctional, spinWeight, spinVector, icoVector, signValue, dot,
    Fin.sum_univ_three, Fin.sum_univ_two, Fintype.sum_prod_type, Fintype.sum_option]
  ring_nf
  field_simp [ne_of_gt radius_pos]
  ring_nf
  simp only [radius_sq, radius_fourth, golden_sq, golden_cube, golden_fourth]
  ring

theorem site_cubic_first_U (a b c : Vec3) (i : Fin 3) :
    siteFunctional .U (fun n => n i *
      ((1 + dot n a) * (1 + dot n b) * (1 + dot n c))) =
      (5 * (a i + b i + c i) + a i * dot b c + b i * dot a c +
        c i * dot a b) / 15 := by
  fin_cases i <;>
    norm_num [siteFunctional, spinWeight, spinVector, icoVector, signValue, dot,
      Fin.sum_univ_three, Fin.sum_univ_two, Fintype.sum_prod_type, Fintype.sum_option] <;>
    ring_nf <;> field_simp [ne_of_gt radius_pos] <;> ring_nf <;>
    simp only [radius_sq, radius_fourth, golden_sq, golden_cube, golden_fourth] <;>
    ring_nf <;> simp only [golden_sq] <;> ring

#print axioms ico_unit
#print axioms site_cubic_U
#print axioms site_cubic_first_U

end AKLT.W.REC021
