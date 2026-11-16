import AKLT.W.REC012.Local

noncomputable section
open scoped BigOperators
open AKLT.Defs
namespace AKLT.W.REC012

lemma moment_coord_one (i : Fin 3) : moment (fun n => n i) = 0 := by
  fin_cases i <;>
    simp [moment, icoVector, signValue, Fintype.sum_prod_type,
      Fin.sum_univ_three, Fin.sum_univ_two] <;> ring

lemma moment_coord_two (i j : Fin 3) :
    moment (fun n => n i * n j) = if i = j then 1 / 3 else 0 := by
  have hr : icoRadius ≠ 0 := by
    have hp : 0 ≤ goldenRatio := by unfold goldenRatio; positivity
    exact ne_of_gt (Real.sqrt_pos.2 (by linarith) : 0 < Real.sqrt (goldenRatio + 2))
  have hsq : icoRadius ^ 2 = 1 + goldenRatio ^ 2 := by
    rw [icoRadius_sq, goldenRatio_sq]; ring
  fin_cases i <;> fin_cases j <;>
    simp [moment, icoVector, signValue, Fintype.sum_prod_type,
      Fin.sum_univ_three, Fin.sum_univ_two] <;>
    field_simp <;> nlinarith [hsq]

lemma moment_coord_three (i j k : Fin 3) :
    moment (fun n => n i * n j * n k) = 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [moment, icoVector, signValue, Fintype.sum_prod_type,
      Fin.sum_univ_three, Fin.sum_univ_two] <;> ring

lemma moment_one : moment (fun _ => 1) = 1 := by
  norm_num [moment, Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two]

lemma moment_add (f g : Vec3 → ℝ) : moment (fun n => f n + g n) = moment f + moment g := by
  simp [moment, Finset.sum_add_distrib, mul_add]
lemma moment_scale (c : ℝ) (f : Vec3 → ℝ) :
    moment (fun n => c * f n) = c * moment f := by
  simp [moment, ← Finset.mul_sum]; ring
lemma moment_sum {ι : Type*} [Fintype ι] (f : ι → Vec3 → ℝ) :
    moment (fun n => ∑ i, f i n) = ∑ i, moment (f i) := by
  simp only [moment, Finset.mul_sum]
  exact Finset.sum_comm

lemma moment_dot (a : Vec3) : moment (fun n => dot n a) = 0 := by
  unfold dot
  simp_rw [mul_comm (_ : ℝ) (a _)]
  rw [moment_sum]
  simp_rw [moment_scale, moment_coord_one, mul_zero]
  simp

lemma moment_dot_two (a b : Vec3) :
    moment (fun n => dot n a * dot n b) = dot a b / 3 := by
  have he (n : Vec3) : dot n a * dot n b =
      ∑ i, ∑ j, (a i * b j) * (n i * n j) := by
    simp only [dot, Fin.sum_univ_three]; ring
  simp_rw [he, moment_sum, moment_scale, moment_coord_two]
  simp [dot, mul_ite, div_eq_mul_inv, Finset.sum_mul]

lemma moment_dot_three (a b c : Vec3) :
    moment (fun n => dot n a * dot n b * dot n c) = 0 := by
  have he (n : Vec3) : dot n a * dot n b * dot n c =
      ∑ i, ∑ j, ∑ k, (a i * b j * c k) * (n i * n j * n k) := by
    simp only [dot, Fin.sum_univ_three]; ring
  simp_rw [he, moment_sum, moment_scale, moment_coord_three, mul_zero]
  simp

lemma site_U (f : Vec3 → ℝ) : siteFunctional .U f = moment f := by
  simp [siteFunctional, Fintype.sum_option, spinWeight, spinVector, moment, Finset.mul_sum]
lemma site_D (f : Vec3 → ℝ) :
    siteFunctional .D f = (2 / 5 : ℝ) * f 0 + (3 / 5 : ℝ) * moment f := by
  simp [siteFunctional, Fintype.sum_option, spinWeight, spinVector, moment, Finset.mul_sum]
  congr 1
  funext j
  ring

lemma moment_local_one (a : Vec3) : moment (fun n => 1 + dot n a) = 1 := by
  rw [moment_add, moment_one, moment_dot]; ring
lemma moment_local_two (a b : Vec3) :
    moment (fun n => (1 + dot n a) * (1 + dot n b)) = 1 + dot a b / 3 := by
  have he (n : Vec3) : (1 + dot n a) * (1 + dot n b) =
      1 + dot n a + dot n b + dot n a * dot n b := by ring
  simp_rw [he, moment_add, moment_one, moment_dot, moment_dot_two]
  ring
lemma moment_local_three (a b c : Vec3) :
    moment (fun n => (1 + dot n a) * (1 + dot n b) * (1 + dot n c)) =
      1 + (dot a b + dot a c + dot b c) / 3 := by
  have he (n : Vec3) : (1 + dot n a) * (1 + dot n b) * (1 + dot n c) =
      1 + dot n a + dot n b + dot n c + dot n a * dot n b +
        dot n a * dot n c + dot n b * dot n c + dot n a * dot n b * dot n c := by ring
  simp_rw [he, moment_add, moment_one, moment_dot, moment_dot_two, moment_dot_three]
  ring

end AKLT.W.REC012
