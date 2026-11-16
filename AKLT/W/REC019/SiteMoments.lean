import AKLT.W.REC019.SpinGeometry

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC019

theorem moment_constant : moment (fun _ => 1) = 1 := by
  norm_num [moment, Fintype.card_prod, IcoLetter]

theorem moment_first (i : Fin 3) : moment (fun n => n i) = 0 := by
  fin_cases i <;>
    simp [moment, Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two,
      icoVector, signValue] <;> ring

theorem moment_second (i j : Fin 3) :
    moment (fun n => n i * n j) = if i = j then 1 / 3 else 0 := by
  have hr := icoRadius_square
  have hp := goldenRatio_square
  have hn := ne_of_gt icoRadius_positive
  fin_cases i <;> fin_cases j <;>
    simp [moment, Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two,
      icoVector, signValue] <;> field_simp <;> nlinarith

theorem moment_third (i j k : Fin 3) : moment (fun n => n i * n j * n k) = 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [moment, Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two,
      icoVector, signValue] <;> ring

set_option maxHeartbeats 800000 in
theorem moment_fourth (i j k l : Fin 3) :
    moment (fun n => n i * n j * n k * n l) =
      ((if i = j ∧ k = l then 1 else 0) + (if i = k ∧ j = l then 1 else 0) +
        (if i = l ∧ j = k then 1 else 0)) / 15 := by
  have hr := icoRadius_square
  have hp := goldenRatio_square
  have hn := ne_of_gt icoRadius_positive
  have hr4 : icoRadius ^ 4 = 5 * goldenRatio ^ 2 := by
    calc
      icoRadius ^ 4 = (icoRadius ^ 2)^2 := by ring
      _ = (goldenRatio + 2)^2 := by rw [hr]
      _ = 5 * goldenRatio ^ 2 := by nlinarith
  have hp4 : goldenRatio ^ 4 = 3 * goldenRatio + 2 := by
    calc
      goldenRatio ^ 4 = (goldenRatio ^ 2)^2 := by ring
      _ = (goldenRatio + 1)^2 := by rw [hp]
      _ = 3 * goldenRatio + 2 := by nlinarith
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [moment, Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two,
      icoVector, signValue] <;> field_simp <;> nlinarith

theorem site_U_eq_moment (f : Vec3 → ℝ) : siteFunctional .U f = moment f := by
  simp [siteFunctional, moment, Fintype.sum_option, spinWeight, spinVector,
    Finset.mul_sum]

theorem site_D_eq_moment (f : Vec3 → ℝ) :
    siteFunctional .D f = (2 / 5 : ℝ) * f 0 + (3 / 5 : ℝ) * moment f := by
  simp only [siteFunctional, moment, Fintype.sum_option, spinWeight, spinVector,
    ite_true, reduceCtorEq, ite_false]
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  ring

end AKLT.W.REC019
