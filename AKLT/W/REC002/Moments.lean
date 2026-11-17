module
public import AKLT.Blueprint.Rec.NodesResponse

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC002

open AKLT.Blueprint.Rec

theorem golden_sq : goldenRatio ^ 2 = goldenRatio + 1 := by
  unfold goldenRatio
  have hs : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith

theorem golden_pos : 0 < goldenRatio := by
  unfold goldenRatio
  positivity

theorem radius_sq : icoRadius ^ 2 = goldenRatio + 2 := by
  unfold icoRadius
  exact Real.sq_sqrt (by linarith [golden_pos])

theorem radius_ne : icoRadius ≠ 0 := by
  have hp : 0 < icoRadius := by
    unfold icoRadius
    exact Real.sqrt_pos.2 (by linarith [golden_pos])
  exact ne_of_gt hp

theorem moment_coordinate (i : Fin 3) : moment (fun v => v i) = 0 := by
  fin_cases i <;>
    simp [moment, icoVector, signValue, Fintype.sum_prod_type,
      Fin.sum_univ_succ] <;> ring

theorem moment_pair_diag (i : Fin 3) : moment (fun v => v i ^ 2) = 1 / 3 := by
  fin_cases i <;>
    simp [moment, icoVector, signValue, Fintype.sum_prod_type,
      Fin.sum_univ_succ] <;>
    field_simp [radius_ne] <;>
    ring_nf <;>
    nlinarith [golden_sq, radius_sq]

theorem moment_coord_pair (i j : Fin 3) :
    moment (fun v => v i * v j) = if i = j then 1 / 3 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [moment, icoVector, signValue, Fintype.sum_prod_type,
      Fin.sum_univ_succ] <;>
    field_simp [radius_ne] <;> ring_nf <;>
    nlinarith [golden_sq, radius_sq]

theorem moment_coord_triple (i j k : Fin 3) :
    moment (fun v => v i * v j * v k) = 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [moment, icoVector, signValue, Fintype.sum_prod_type,
      Fin.sum_univ_succ] <;> ring

theorem ico_unit (j : IcoLetter) : normSq (icoVector j) = 1 := by
  rcases j with ⟨a, b, c⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [normSq, dot, Fin.sum_univ_three, icoVector, signValue] <;>
    field_simp [radius_ne] <;> nlinarith [golden_sq, radius_sq]

theorem spin_ball (j : SpinLetter) : normSq (spinVector j) ≤ 1 := by
  cases j with
  | none => norm_num [spinVector, normSq, dot]
  | some j => exact (ico_unit j).le

theorem norm_nonneg (a : Vec3) : 0 ≤ normSq a := by
  change 0 ≤ ∑ i, a i * a i
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (a i))

theorem factor_nonneg (a b : Vec3) (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) :
    0 ≤ 1 + dot a b := by
  have hcs : dot a b ^ 2 ≤ normSq a * normSq b := by
    simpa [dot, normSq, ← pow_two] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  have hmul : normSq a * normSq b ≤ 1 :=
    (mul_le_mul ha hb (norm_nonneg b) (by norm_num)).trans_eq (by norm_num)
  nlinarith [sq_nonneg (dot a b + 1)]

theorem dot_comm (a b : Vec3) : dot a b = dot b a := by
  simp only [dot, mul_comm]

theorem moment_add (f g : Vec3 → ℝ) :
    moment (fun n => f n + g n) = moment f + moment g := by
  simp [moment, Finset.sum_add_distrib, mul_add]

theorem moment_smul (c : ℝ) (f : Vec3 → ℝ) :
    moment (fun n => c * f n) = c * moment f := by
  simp [moment, ← Finset.mul_sum, mul_left_comm]

theorem moment_sum {ι : Type*} [Fintype ι] (f : ι → Vec3 → ℝ) :
    moment (fun n => ∑ i, f i n) = ∑ i, moment (f i) := by
  simp only [moment, Finset.mul_sum]
  exact Finset.sum_comm

theorem moment_one : moment (fun _ => 1) = 1 := by
  norm_num [moment, IcoLetter, Fintype.card_prod]

theorem moment_dot (a : Vec3) : moment (fun n => dot n a) = 0 := by
  have he : (fun n => dot n a) = (fun n => ∑ i, a i * n i) := by
    funext n; simp [dot, mul_comm]
  rw [he, moment_sum]
  simp only [moment_smul, moment_coordinate, mul_zero, Finset.sum_const_zero]

theorem moment_dot_pair (a b : Vec3) :
    moment (fun n => dot n a * dot n b) = dot a b / 3 := by
  have he : (fun n => dot n a * dot n b) =
      (fun n => ∑ i, ∑ j, (a i * b j) * (n i * n j)) := by
    funext n; simp [dot, Fin.sum_univ_three]; ring
  rw [he, moment_sum]
  simp_rw [moment_sum, moment_smul, moment_coord_pair]
  simp [dot, div_eq_mul_inv, Finset.sum_mul, mul_assoc]

theorem moment_dot_triple (a b c : Vec3) :
    moment (fun n => dot n a * dot n b * dot n c) = 0 := by
  have he : (fun n => dot n a * dot n b * dot n c) =
      (fun n => ∑ i, ∑ j, ∑ k, (a i * b j * c k) * (n i * n j * n k)) := by
    funext n; simp [dot, Fin.sum_univ_three]; ring
  rw [he, moment_sum]
  simp_rw [moment_sum, moment_smul, moment_coord_triple, mul_zero, Finset.sum_const_zero]

theorem siteU (f : Vec3 → ℝ) : siteFunctional .U f = moment f := by
  simp [siteFunctional, Fintype.sum_option, spinWeight, spinVector, moment, Finset.mul_sum]

theorem siteD (f : Vec3 → ℝ) :
    siteFunctional .D f = (3 / 5) * moment f + (2 / 5) * f 0 := by
  simp [siteFunctional, Fintype.sum_option, spinWeight, spinVector, moment,
    ← Finset.mul_sum]
  ring

theorem integrate_U3 (a b c : Vec3) :
    siteFunctional .U (fun n => (1 + dot n a) * (1 + dot n b) * (1 + dot n c)) =
      1 + (dot a b + dot a c + dot b c) / 3 := by
  have he : (fun n => (1 + dot n a) * (1 + dot n b) * (1 + dot n c)) =
      (fun n => 1 + dot n a + dot n b + dot n c + dot n a * dot n b +
        dot n a * dot n c + dot n b * dot n c + dot n a * dot n b * dot n c) := by
    funext n; ring
  rw [siteU, he]
  simp only [moment_add, moment_one, moment_dot, moment_dot_pair, moment_dot_triple]
  ring

theorem integrate_D2 (a b : Vec3) :
    siteFunctional .D (fun n => (1 + dot n a) * (1 + dot n b)) = 1 + dot a b / 5 := by
  have he : (fun n => (1 + dot n a) * (1 + dot n b)) =
      (fun n => 1 + dot n a + dot n b + dot n a * dot n b) := by funext n; ring
  rw [siteD, he]
  simp only [moment_add, moment_one, moment_dot, moment_dot_pair]
  simp [dot]
  ring

end AKLT.W.REC002
