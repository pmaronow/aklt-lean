module
public import AKLT.Defs.Moment

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC003

theorem phi_sq : goldenRatio ^ 2 = goldenRatio + 1 := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  dsimp [goldenRatio]
  nlinarith

theorem radius_pos : 0 < icoRadius := by
  apply Real.sqrt_pos.2
  have h := Real.sqrt_nonneg (5 : ℝ)
  dsimp [goldenRatio]
  linarith

theorem radius_sq : icoRadius ^ 2 = goldenRatio + 2 := by
  apply Real.sq_sqrt
  have h := Real.sqrt_nonneg (5 : ℝ)
  dsimp [goldenRatio]
  linarith

theorem ico_unit (j : IcoLetter) : normSq (icoVector j) = 1 := by
  rcases j with ⟨a, b, c⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    norm_num [normSq, dot, Fin.sum_univ_succ, icoVector, signValue] <;>
    field_simp [ne_of_gt radius_pos] <;> nlinarith [phi_sq, radius_sq]

theorem spin_ball (j : SpinLetter) : normSq (spinVector j) ≤ 1 := by
  cases j with
  | none => norm_num [spinVector, normSq, dot]
  | some j => exact (ico_unit j).le

theorem factor_nonneg (a b : Vec3) (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) :
    0 ≤ 1 + dot a b := by
  have h : 0 ≤ ∑ i : Fin 3, (a i + b i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg (a i + b i)
  have heq : (∑ i : Fin 3, (a i + b i) ^ 2) = normSq a + normSq b + 2 * dot a b := by
    simp only [normSq, dot, Fin.sum_univ_succ]
    ring
  rw [heq] at h
  linarith

theorem dot_comm (a b : Vec3) : dot a b = dot b a := by
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem site_add (s : Status) (f g : Vec3 → ℝ) :
    siteFunctional s (fun v => f v + g v) = siteFunctional s f + siteFunctional s g := by
  simp [siteFunctional, mul_add, Finset.sum_add_distrib]

theorem site_mul_const (s : Status) (f : Vec3 → ℝ) (c : ℝ) :
    siteFunctional s (fun v => f v * c) = siteFunctional s f * c := by
  simp only [siteFunctional, ← mul_assoc, Finset.sum_mul]

theorem site_sum {ι : Type*} [Fintype ι] (s : Status) (f : ι → Vec3 → ℝ) :
    siteFunctional s (fun v => ∑ i, f i v) = ∑ i, siteFunctional s (f i) := by
  simp only [siteFunctional, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem site_const (s : Status) (hs : s = .U ∨ s = .D) :
    siteFunctional s (fun _ => 1) = 1 := by
  rcases hs with rfl | rfl <;>
    norm_num [siteFunctional, Fintype.sum_option, spinWeight, spinVector,
      IcoLetter, Fintype.card_prod]

theorem site_coord (s : Status) (i : Fin 3) :
    siteFunctional s (fun v => v i) = 0 := by
  cases s <;> fin_cases i <;>
    norm_num [siteFunctional, Fintype.sum_option, Fintype.sum_prod_type,
      Fin.sum_univ_succ, spinWeight, spinVector, icoVector, signValue] <;> ring

theorem site_U_coord_pair (i j : Fin 3) :
    siteFunctional .U (fun v => v i * v j) = if i = j then 1 / 3 else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [siteFunctional, Fintype.sum_option, Fintype.sum_prod_type,
      Fin.sum_univ_succ, spinWeight, spinVector, icoVector, signValue] <;>
    field_simp [ne_of_gt radius_pos] <;> nlinarith [phi_sq, radius_sq]

theorem site_linear (s : Status) (a : Vec3) :
    siteFunctional s (fun v => dot v a) = 0 := by
  simp only [dot, site_sum, site_mul_const, site_coord, zero_mul, Finset.sum_const_zero]

theorem site_U_cross (a b : Vec3) :
    siteFunctional .U (fun v => dot v a * dot v b) = dot a b / 3 := by
  simp only [dot, Finset.sum_mul, Finset.mul_sum, site_sum]
  simp_rw [show ∀ (v : Vec3) (i j : Fin 3),
    v i * a i * (v j * b j) = (v i * v j) * (a i * b j) by intros; ring]
  simp only [site_mul_const, site_U_coord_pair]
  simp [div_eq_mul_inv, mul_comm, mul_assoc, Finset.mul_sum]

theorem site_U_two (a b : Vec3) :
    siteFunctional .U (fun v => (1 + dot v a) * (1 + dot v b)) = 1 + dot a b / 3 := by
  have heq : (fun v => (1 + dot v a) * (1 + dot v b)) =
      (fun v => (1 + dot v a) + dot v b + dot v a * dot v b) := by
    funext v
    ring
  rw [heq, site_add, site_add, site_add, site_const .U (Or.inl rfl),
    site_linear, site_linear, site_U_cross]
  ring

theorem site_D_one (a : Vec3) :
    siteFunctional .D (fun v => 1 + dot v a) = 1 := by
  rw [site_add, site_const .D (Or.inr rfl), site_linear, add_zero]

end AKLT.W.REC003
