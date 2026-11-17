module
public import AKLT.W.REC005.Local

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000

namespace AKLT.W.REC005

lemma moment_add (f g : Vec3 → ℝ) :
    moment (fun v => f v + g v) = moment f + moment g := by
  simp [moment, Finset.sum_add_distrib, mul_add]

lemma moment_const_mul (r : ℝ) (f : Vec3 → ℝ) :
    moment (fun v => r * f v) = r * moment f := by
  simp [moment, ← Finset.mul_sum]
  ring

lemma moment_mul_const (f : Vec3 → ℝ) (r : ℝ) :
    moment (fun v => f v * r) = moment f * r := by
  simpa only [mul_comm] using moment_const_mul r f

lemma moment_sum {ι : Type*} [Fintype ι] (f : ι → Vec3 → ℝ) :
    moment (fun v => ∑ i, f i v) = ∑ i, moment (f i) := by
  classical
  simp only [moment, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma moment_one : moment (fun _ => 1) = 1 := by
  norm_num [moment, Fintype.card_prod, IcoLetter]

lemma moment_dot (a : Vec3) : moment (fun v => dot v a) = 0 := by
  simp [dot, moment_sum, moment_mul_const, moment_first]

lemma moment_dot_two (a b : Vec3) :
    moment (fun v => dot v a * dot v b) = dot a b / 3 := by
  have heq : (fun v => dot v a * dot v b) =
      fun v => ∑ i, ∑ j, (v i * v j) * (a i * b j) := by
    funext v
    simp only [dot, Fin.sum_univ_three]
    ring
  rw [heq]
  simp [moment_sum, moment_mul_const, moment_second, dot, Finset.sum_div,
    mul_div_assoc, ite_mul]
  simp only [Fin.sum_univ_three]
  ring

lemma moment_dot_three (a b c : Vec3) :
    moment (fun v => dot v a * dot v b * dot v c) = 0 := by
  have heq : (fun v => dot v a * dot v b * dot v c) =
      fun v => ∑ i, ∑ j, ∑ k, (v i * v j * v k) * (a i * b j * c k) := by
    funext v
    simp only [dot, Fin.sum_univ_three]
    ring
  rw [heq]
  simp [moment_sum, moment_mul_const, moment_third]

lemma moment_coord_dot (i : Fin 3) (a : Vec3) :
    moment (fun v => v i * dot v a) = a i / 3 := by
  have heq : (fun v => v i * dot v a) = fun v => ∑ j, (v i * v j) * a j := by
    funext v
    simp [dot, Finset.mul_sum, mul_assoc]
  rw [heq]
  simp [moment_sum, moment_mul_const, moment_second, ite_mul]
  ring

lemma moment_coord_dot_two (i : Fin 3) (a b : Vec3) :
    moment (fun v => v i * dot v a * dot v b) = 0 := by
  have heq : (fun v => v i * dot v a * dot v b) =
      fun v => ∑ j, ∑ k, (v i * v j * v k) * (a j * b k) := by
    funext v
    simp only [dot, Fin.sum_univ_three]
    ring
  rw [heq]
  simp [moment_sum, moment_mul_const, moment_third]

lemma moment_coord_dot_three (i : Fin 3) (a b c : Vec3) :
    moment (fun v => v i * dot v a * dot v b * dot v c) =
      (a i * dot b c + b i * dot a c + c i * dot a b) / 15 := by
  have heq : (fun v => v i * dot v a * dot v b * dot v c) =
      fun v => ∑ j, ∑ k, ∑ l, (v i * v j * v k * v l) * (a j * b k * c l) := by
    funext v
    simp only [dot, Fin.sum_univ_three]
    ring
  rw [heq]
  simp only [moment_sum, moment_mul_const, moment_fourth]
  fin_cases i <;>
    simp [Fin.sum_univ_three, dot] <;> ring

def tripleWeight (a b c : Vec3) (v : Vec3) : ℝ :=
  (1 + dot v a) * (1 + dot v b) * (1 + dot v c)

def tripleP (a b c : Vec3) : ℝ := dot a b + dot a c + dot b c

def tripleV (a b c : Vec3) : Vec3 := fun i =>
  5 * (a i + b i + c i) + a i * dot b c + b i * dot a c + c i * dot a b

lemma triple_normalizer (a b c : Vec3) :
    moment (tripleWeight a b c) = 1 + tripleP a b c / 3 := by
  have heq : tripleWeight a b c = fun v =>
      1 + dot v a + dot v b + dot v c + dot v a * dot v b +
        dot v a * dot v c + dot v b * dot v c + dot v a * dot v b * dot v c := by
    funext v
    unfold tripleWeight
    ring
  rw [heq]
  simp only [moment_add, moment_one, moment_dot, moment_dot_two, moment_dot_three]
  unfold tripleP
  ring

lemma triple_numerator (a b c : Vec3) (i : Fin 3) :
    15 * moment (fun v => v i * tripleWeight a b c v) = tripleV a b c i := by
  have heq : (fun v => v i * tripleWeight a b c v) = fun v =>
      v i + v i * dot v a + v i * dot v b + v i * dot v c +
        v i * dot v a * dot v b + v i * dot v a * dot v c +
        v i * dot v b * dot v c + v i * dot v a * dot v b * dot v c := by
    funext v
    unfold tripleWeight
    ring
  rw [heq]
  simp only [moment_add, moment_first, moment_coord_dot, moment_coord_dot_two,
    moment_coord_dot_three]
  unfold tripleV
  ring

end AKLT.W.REC005
