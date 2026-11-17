module
public import AKLT.W.REC019.SiteMoments

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC019

private theorem moment_add (f g : Vec3 → ℝ) :
    moment (fun n => f n + g n) = moment f + moment g := by
  simp [moment, Finset.sum_add_distrib, mul_add]

private theorem moment_const_mul (a : ℝ) (f : Vec3 → ℝ) :
    moment (fun n => a * f n) = a * moment f := by
  simp only [moment, ← Finset.mul_sum]
  ring

private theorem moment_sum {ι : Type*} (S : Finset ι) (f : ι → Vec3 → ℝ) :
    moment (fun n => ∑ i ∈ S, f i n) = ∑ i ∈ S, moment (f i) := by
  unfold moment
  rw [Finset.sum_comm, Finset.mul_sum]

private theorem moment_dot (a : Vec3) : moment (fun n => dot n a) = 0 := by
  have he : (fun n => dot n a) = fun n => ∑ i, a i * n i := by
    funext n
    simp [dot, mul_comm]
  rw [he, moment_sum]
  simp only [moment_const_mul, moment_first, mul_zero, Finset.sum_const_zero]

private theorem moment_twoDot (a b : Vec3) :
    moment (fun n => dot n a * dot n b) = dot a b / 3 := by
  have he : (fun n => dot n a * dot n b) =
      fun n => ∑ i : Fin 3, ∑ j : Fin 3, (a i * b j) * (n i * n j) := by
    funext n
    simp [dot, Fin.sum_univ_three]
    ring
  rw [he]
  simp only [moment_sum, moment_const_mul, moment_second]
  simp [Fin.sum_univ_three, dot]
  ring

private theorem moment_threeDot (a b c : Vec3) :
    moment (fun n => dot n a * dot n b * dot n c) = 0 := by
  have he : (fun n => dot n a * dot n b * dot n c) =
      fun n => ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        (a i * b j * c k) * (n i * n j * n k) := by
    funext n
    simp [dot, Fin.sum_univ_three]
    ring
  rw [he]
  simp only [moment_sum, moment_const_mul, moment_third, mul_zero, Finset.sum_const_zero]

private theorem moment_coord_dot (i : Fin 3) (a : Vec3) :
    moment (fun n => n i * dot n a) = a i / 3 := by
  have he : (fun n => n i * dot n a) =
      fun n => ∑ j : Fin 3, a j * (n i * n j) := by
    funext n
    simp [dot, Fin.sum_univ_three]
    ring
  rw [he, moment_sum]
  simp only [moment_const_mul, moment_second]
  fin_cases i <;> simp <;> ring

private theorem moment_coord_twoDot (i : Fin 3) (a b : Vec3) :
    moment (fun n => n i * dot n a * dot n b) = 0 := by
  have he : (fun n => n i * dot n a * dot n b) =
      fun n => ∑ j : Fin 3, ∑ k : Fin 3, (a j * b k) * (n i * n j * n k) := by
    funext n
    simp [dot, Fin.sum_univ_three]
    ring
  rw [he]
  simp only [moment_sum, moment_const_mul, moment_third, mul_zero, Finset.sum_const_zero]

private theorem moment_coord_threeDot (i : Fin 3) (a b c : Vec3) :
    moment (fun n => n i * dot n a * dot n b * dot n c) =
      (a i * dot b c + b i * dot a c + c i * dot a b) / 15 := by
  have he : (fun n => n i * dot n a * dot n b * dot n c) =
      fun n => ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
        (a j * b k * c l) * (n i * n j * n k * n l) := by
    funext n
    simp [dot, Fin.sum_univ_three]
    ring
  rw [he]
  simp only [moment_sum, moment_const_mul, moment_fourth]
  fin_cases i <;> simp [Fin.sum_univ_three, dot] <;> ring

def threeProduct (a b c n : Vec3) : ℝ :=
  (1 + dot n a) * (1 + dot n b) * (1 + dot n c)

def tripleP (a b c : Vec3) : ℝ := dot a b + dot a c + dot b c

def tripleV (a b c : Vec3) : Vec3 :=
  fun i => 5 * (a i + b i + c i) + a i * dot b c + b i * dot a c + c i * dot a b

theorem moment_threeProduct (a b c : Vec3) :
    moment (threeProduct a b c) = 1 + tripleP a b c / 3 := by
  have he : threeProduct a b c = fun n =>
      1 + dot n a + dot n b + dot n c + dot n a * dot n b +
        dot n a * dot n c + dot n b * dot n c + dot n a * dot n b * dot n c := by
    funext n
    unfold threeProduct
    ring
  rw [he]
  simp only [moment_add, moment_constant, moment_dot, moment_twoDot, moment_threeDot]
  unfold tripleP
  ring

theorem moment_coord_threeProduct (a b c : Vec3) (i : Fin 3) :
    moment (fun n => n i * threeProduct a b c n) = tripleV a b c i / 15 := by
  have he : (fun n => n i * threeProduct a b c n) = fun n =>
      n i + n i * dot n a + n i * dot n b + n i * dot n c +
        n i * dot n a * dot n b + n i * dot n a * dot n c +
        n i * dot n b * dot n c + n i * dot n a * dot n b * dot n c := by
    funext n
    unfold threeProduct
    ring
  rw [he]
  simp only [moment_add, moment_first, moment_coord_dot, moment_coord_twoDot,
    moment_coord_threeDot]
  unfold tripleV
  ring

end AKLT.W.REC019
