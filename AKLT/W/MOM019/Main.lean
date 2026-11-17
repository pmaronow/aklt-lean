module
public import AKLT.Blueprint.Mom.NodesMean

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Mom

namespace AKLT.W.MOM019

lemma phi_sq : goldenRatio ^ 2 = goldenRatio + 1 := by
  unfold goldenRatio
  have hs : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith

lemma radius_sq : icoRadius ^ 2 = goldenRatio + 2 := by
  unfold icoRadius
  exact Real.sq_sqrt (by unfold goldenRatio; positivity)

lemma radius_ne : icoRadius ≠ 0 := by
  have h : 0 < icoRadius := Real.sqrt_pos.2 (by unfold goldenRatio; positivity)
  linarith

lemma ico_second (i j : Fin 3) : moment (fun v => v i * v j) = if i = j then 1/3 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [moment, IcoLetter, icoVector, signValue, Fintype.sum_prod_type,
      Fin.sum_univ_three] <;>
    field_simp [radius_ne] <;> nlinarith [phi_sq, radius_sq]

lemma phi_fourth : goldenRatio ^ 4 = 3 * goldenRatio + 2 := by
  calc
    goldenRatio ^ 4 = (goldenRatio ^ 2) ^ 2 := by ring
    _ = (goldenRatio + 1) ^ 2 := by rw [phi_sq]
    _ = 3 * goldenRatio + 2 := by nlinarith [phi_sq]

lemma radius_fourth : icoRadius ^ 4 = 5 * (goldenRatio + 1) := by
  calc
    icoRadius ^ 4 = (icoRadius ^ 2) ^ 2 := by ring
    _ = (goldenRatio + 2) ^ 2 := by rw [radius_sq]
    _ = 5 * (goldenRatio + 1) := by nlinarith [phi_sq]

set_option maxHeartbeats 1000000 in
lemma ico_fourth (i j k l : Fin 3) :
    moment (fun v => v i * v j * v k * v l) =
      ((if i = j ∧ k = l then 1 else 0) +
        (if i = k ∧ j = l then 1 else 0) +
        (if i = l ∧ j = k then 1 else 0)) / 15 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [moment, IcoLetter, icoVector, signValue, Fintype.sum_prod_type,
      Fin.sum_univ_three] <;>
    field_simp [radius_ne] <;> nlinarith [phi_sq, radius_sq, phi_fourth, radius_fourth]

lemma ico_first (i : Fin 3) : moment (fun v => v i) = 0 := by
  fin_cases i <;>
    simp [moment, IcoLetter, icoVector, signValue, Fintype.sum_prod_type,
      Fin.sum_univ_three] <;>
    field_simp [radius_ne] <;> ring

lemma ico_third (i j k : Fin 3) : moment (fun v => v i * v j * v k) = 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [moment, IcoLetter, icoVector, signValue, Fintype.sum_prod_type,
      Fin.sum_univ_three] <;>
    field_simp [radius_ne] <;> ring

lemma ico_tensor_law : TensorLaw moment 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact momentConstant
  · exact ico_first
  · exact ico_third
  · intro i j
    simpa using ico_second i j
  · intro i j k l
    simpa using ico_fourth i j k l

lemma moment_sum {α : Type} [Fintype α] (f : α → Vec3 → ℝ) :
    moment (fun v => ∑ x, f x v) = ∑ x, moment (f x) := by
  unfold moment
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]

lemma moment_const_mul (c : ℝ) (f : Vec3 → ℝ) :
    moment (fun v => c * f v) = c * moment f := by
  unfold moment
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

lemma moment_add (f g : Vec3 → ℝ) :
    moment (fun v => f v + g v) = moment f + moment g := by
  unfold moment
  simp [Finset.sum_add_distrib, mul_add]

lemma moment_linear_dot (i : Fin 3) (a : Vec3) :
    moment (fun v => v i * dot v a) = a i / 3 := by
  have hexp : (fun v => v i * dot v a) =
      fun v => ∑ j : Fin 3, a j * (v i * v j) := by
    funext v
    simp only [dot]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hexp, moment_sum]
  simp_rw [moment_const_mul, ico_second]
  fin_cases i <;> simp <;> ring_nf

lemma moment_linear_dot_pair (i : Fin 3) (a b : Vec3) :
    moment (fun v => v i * dot v a * dot v b) = 0 := by
  have hexp : (fun v => v i * dot v a * dot v b) =
      fun v => ∑ j : Fin 3, ∑ k : Fin 3,
        (a k * b j) * (v i * v k * v j) := by
    funext v
    simp only [dot]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hexp, moment_sum]
  simp_rw [moment_sum, moment_const_mul, ico_third]
  simp

lemma moment_linear_dot_triple (i : Fin 3) (a b c : Vec3) :
    moment (fun v => v i * dot v a * dot v b * dot v c) =
      (a i * dot b c + b i * dot a c + c i * dot a b) / 15 := by
  have hexp : (fun v => v i * dot v a * dot v b * dot v c) =
      fun v => ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
        (a l * b k * c j) * (v i * v l * v k * v j) := by
    funext v
    simp only [dot]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l hl
    ring
  rw [hexp, moment_sum]
  simp_rw [moment_sum, moment_const_mul, ico_fourth]
  fin_cases i <;> simp [Fin.sum_univ_three, dot] <;> ring

lemma moment_local_triple (a : Fin 3 → Vec3) (i : Fin 3) :
    moment (fun v => v i * localProduct a v) =
      (a 0 i + a 1 i + a 2 i) / 3 +
        (a 0 i * dot (a 1) (a 2) + a 1 i * dot (a 0) (a 2) +
          a 2 i * dot (a 0) (a 1)) / 15 := by
  have hexp : (fun v => v i * localProduct a v) = fun v =>
      v i +
        (v i * dot v (a 0) + v i * dot v (a 1) + v i * dot v (a 2)) +
        (v i * dot v (a 0) * dot v (a 1) +
          v i * dot v (a 0) * dot v (a 2) +
          v i * dot v (a 1) * dot v (a 2)) +
        v i * dot v (a 0) * dot v (a 1) * dot v (a 2) := by
    funext v
    simp only [localProduct, Fin.prod_univ_three]
    ring
  rw [hexp]
  simp only [moment_add, ico_first, moment_linear_dot, moment_linear_dot_pair,
    moment_linear_dot_triple]
  ring

theorem main : AKLT.Blueprint.Mom.TripleNumeratorStatement := by
  intro a i
  have hU : siteFunctional .U (fun v => v i * localProduct a v) =
      moment (fun v => v i * localProduct a v) := by
    simp [siteFunctional, moment, Fintype.sum_option, spinWeight, spinVector]
    rw [← Finset.mul_sum]
  rw [hU, moment_local_triple]
  change 15 * ((a 0 i + a 1 i + a 2 i) / 3 +
      (a 0 i * dot (a 1) (a 2) + a 1 i * dot (a 0) (a 2) +
        a 2 i * dot (a 0) (a 1)) / 15) = _
  simp [AKLT.Blueprint.Mom.tripleV]
  ring

end AKLT.W.MOM019
