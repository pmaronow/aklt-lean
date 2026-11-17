module
public import AKLT.W.H1M047.Basic
public import Mathlib.Algebra.MvPolynomial.Funext

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.H1

namespace AKLT.W.H1M047

@[simp] lemma pauliExponent_apply (J : Finset (Fin 20)) (a : J → Fin 4)
    (v : Fin 20 × Fin 3) :
    pauliExponent J a v =
      if h : v.1 ∈ J then if (a ⟨v.1, h⟩).val = v.2.val + 1 then 1 else 0 else 0 := by
  simp [pauliExponent]

lemma pauliExponent_injective (J : Finset (Fin 20)) :
    Function.Injective (pauliExponent J) := by
  intro a b hab
  funext j
  have h (k : Fin 3) :
      (if (a j).val = k.val + 1 then (1 : ℕ) else 0) =
        (if (b j).val = k.val + 1 then 1 else 0) := by
    simpa only [pauliExponent_apply, j.property, dite_true] using
      congrArg (fun m : (Fin 20 × Fin 3) →₀ ℕ => m (j.val, k)) hab
  have ha := (a j).isLt
  have hb := (b j).isLt
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at h0 h1 h2
  apply Fin.ext
  split_ifs at h0 h1 h2 <;> omega

lemma affine_exponent_exists (J : Finset (Fin 20))
    (m : (Fin 20 × Fin 3) →₀ ℕ)
    (ha : ∀ j : Fin 20, (∑ k : Fin 3, m (j, k)) ≤ 1)
    (hs : ∀ j : Fin 20, j ∉ J → ∀ k : Fin 3, m (j, k) = 0) :
    ∃ a : J → Fin 4, pauliExponent J a = m := by
  let a : J → Fin 4 := fun j =>
    if m (j.val, 0) = 1 then 1 else if m (j.val, 1) = 1 then 2 else
      if m (j.val, 2) = 1 then 3 else 0
  refine ⟨a, ?_⟩
  ext v
  obtain ⟨j, k⟩ := v
  by_cases hj : j ∈ J
  · have h := ha j
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
    simp only [pauliExponent_apply, hj, dite_true]
    norm_num at h
    fin_cases k <;> dsimp [a] <;> split_ifs <;> norm_num at * <;> omega
  · simp [hj, hs j hj k]

lemma polynomial_pauli_expansion (J : Finset (Fin 20)) (p : VectorPolynomial)
    (ha : VectorAffine p) (hs : SupportedVectors J p) :
    p = ∑ a : J → Fin 4, MvPolynomial.monomial (pauliExponent J a)
      (p.coeff (pauliExponent J a)) := by
  classical
  ext m
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  by_cases hm : ∃ a : J → Fin 4, pauliExponent J a = m
  · obtain ⟨b, rfl⟩ := hm
    rw [Finset.sum_eq_single b]
    · simp
    · intro a _ hab
      simp [(pauliExponent_injective J).ne hab]
    · simp
  · have hp : p.coeff m = 0 := by
      by_contra hp
      have hmem := MvPolynomial.mem_support_iff.mpr hp
      exact hm (affine_exponent_exists J m (ha m hmem) (hs m hmem))
    rw [hp]
    symm
    apply Finset.sum_eq_zero
    intro a _
    simp only [show pauliExponent J a ≠ m from fun h => hm ⟨a, h⟩, ite_false]

lemma eval_pauli_monomial (J : Finset (Fin 20)) (a : J → Fin 4)
    (c : ℝ) (u : Fin 20 → Vec3) :
    MvPolynomial.eval (fun v => u v.1 v.2)
        (MvPolynomial.monomial (pauliExponent J a) c) =
      c * ∏ j : J, pauliCoordinate (u j.val) (a j) := by
  classical
  rw [MvPolynomial.eval_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type]
  congr 1
  simp only [Finset.univ_eq_attach]
  rw [Finset.prod_attach_eq_prod_dite]
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : j ∈ J
  · rw [dite_eq_left hj]
    simp only [pauliExponent_apply, hj, dite_true]
    change (∏ k : Fin 3, u j k ^
      (if (a ⟨j, hj⟩).val = k.val + 1 then 1 else 0)) =
        pauliCoordinate (u j) (a ⟨j, hj⟩)
    generalize a ⟨j, hj⟩ = b
    fin_cases b <;> simp [pauliCoordinate, Fin.prod_univ_succ]
  · simp [pauliExponent_apply, hj]

lemma evaluate_pauli_expansion (J : Finset (Fin 20)) (p : VectorPolynomial)
    (ha : VectorAffine p) (hs : SupportedVectors J p) (u : Fin 20 → Vec3) :
    evaluateReduced p u = ∑ a : J → Fin 4,
      (p.coeff (pauliExponent J a) : ℝ) *
        ∏ j : J, pauliCoordinate (u j.val) (a j) := by
  classical
  unfold evaluateReduced
  conv_lhs => rw [polynomial_pauli_expansion J p ha hs]
  rw [MvPolynomial.eval₂_sum]
  simp only [MvPolynomial.eval₂_monomial]
  apply Finset.sum_congr rfl
  intro a _
  simpa [MvPolynomial.eval_monomial] using
    eval_pauli_monomial J a (p.coeff (pauliExponent J a) : ℝ) u

/-- Reconstruct a real polynomial from its Pauli-indexed coefficients. -/
def coefficientPolynomial (J : Finset (Fin 20)) (c : (J → Fin 4) → ℝ) :
    MvPolynomial (Fin 20 × Fin 3) ℝ :=
  ∑ a : J → Fin 4, MvPolynomial.monomial (pauliExponent J a) (c a)

lemma coefficientPolynomial_coeff (J : Finset (Fin 20))
    (c : (J → Fin 4) → ℝ) (b : J → Fin 4) :
    (coefficientPolynomial J c).coeff (pauliExponent J b) = c b := by
  classical
  simp [coefficientPolynomial, (pauliExponent_injective J).eq_iff]

lemma coefficientPolynomial_eval (J : Finset (Fin 20))
    (c : (J → Fin 4) → ℝ) (u : Fin 20 → Vec3) :
    MvPolynomial.eval (fun v => u v.1 v.2) (coefficientPolynomial J c) =
      ∑ a : J → Fin 4, c a * ∏ j : J, pauliCoordinate (u j.val) (a j) := by
  simp only [coefficientPolynomial, MvPolynomial.eval_sum, eval_pauli_monomial]

lemma pauliCoordinate_rotate (R : Matrix (Fin 3) (Fin 3) ℝ) (u : Vec3) (a : Fin 4) :
    pauliCoordinate (R.transpose.mulVec u) a =
      ∑ b : Fin 4, pauliRotationCoefficient R b a * pauliCoordinate u b := by
  fin_cases a <;>
    simp [pauliCoordinate, pauliRotationCoefficient, Matrix.mulVec,
      dotProduct, Matrix.transpose_apply, Fin.sum_univ_succ]

def rotatedCoefficientReal (J : Finset (Fin 20)) (p : VectorPolynomial)
    (R : Matrix (Fin 3) (Fin 3) ℝ) (b : J → Fin 4) : ℝ :=
  ∑ a : J → Fin 4, (p.coeff (pauliExponent J a) : ℝ) *
    ∏ j : J, pauliRotationCoefficient R (b j) (a j)

lemma rotatedCoefficientReal_eval (J : Finset (Fin 20)) (p : VectorPolynomial)
    (ha : VectorAffine p) (hs : SupportedVectors J p)
    (R : Matrix (Fin 3) (Fin 3) ℝ) (u : Fin 20 → Vec3) :
    MvPolynomial.eval (fun v => u v.1 v.2)
        (coefficientPolynomial J (rotatedCoefficientReal J p R)) =
      evaluateReduced p (fun j => R.transpose.mulVec (u j)) := by
  classical
  rw [coefficientPolynomial_eval, evaluate_pauli_expansion J p ha hs]
  simp only [rotatedCoefficientReal, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp_rw [pauliCoordinate_rotate]
  rw [Fintype.prod_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.prod_mul_distrib, mul_assoc]

lemma rotation_coefficients_real (J : Finset (Fin 20)) (p : VectorPolynomial)
    (ha : VectorAffine p) (hs : SupportedVectors J p) (hi : OrthogonalInvariant p)
    (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : R.transpose * R = 1) (b : J → Fin 4) :
    rotatedCoefficientReal J p R b = (p.coeff (pauliExponent J b) : ℝ) := by
  have hR' : R.transpose.transpose * R.transpose = 1 := by
    simpa using (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (Fin 3))).mp hR
  have hpoly : coefficientPolynomial J (rotatedCoefficientReal J p R) =
      MvPolynomial.map (Rat.castHom ℝ) p := by
    apply MvPolynomial.funext
    intro x
    let u : Fin 20 → Vec3 := fun j k => x (j, k)
    change MvPolynomial.eval (fun v : Fin 20 × Fin 3 => u v.1 v.2) _ = _
    rw [rotatedCoefficientReal_eval J p ha hs R u, hi R.transpose hR' u,
      MvPolynomial.eval_map]
    rfl
  have hc := congrArg (fun q : MvPolynomial (Fin 20 × Fin 3) ℝ =>
    q.coeff (pauliExponent J b)) hpoly
  simpa [coefficientPolynomial_coeff, MvPolynomial.coeff_map] using hc

lemma rotation_coefficients (J : Finset (Fin 20)) (p : VectorPolynomial)
    (ha : VectorAffine p) (hs : SupportedVectors J p) (hi : OrthogonalInvariant p)
    (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : R.transpose * R = 1) (b : J → Fin 4) :
    rotatedPauliCoefficient J p R b = (p.coeff (pauliExponent J b) : ℂ) := by
  have hc := congrArg Complex.ofReal (rotation_coefficients_real J p ha hs hi R hR b)
  simpa [rotatedCoefficientReal, rotatedPauliCoefficient] using hc

end AKLT.W.H1M047
