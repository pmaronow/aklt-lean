module
public import AKLT.W.H1M052.Tensor

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs AKLT.Blueprint.H1

namespace AKLT.W.H1M052

abbrev RealPoly := MvPolynomial (Fin 20 × Fin 3) ℝ

def slotExponent (j : Fin 20) (a : Fin 4) : (Fin 20 × Fin 3) →₀ ℕ :=
  if h : a.val = 0 then 0 else Finsupp.single (j, ⟨a.val - 1, by omega⟩) 1

@[simp] theorem slotExponent_apply (j l : Fin 20) (a : Fin 4) (k : Fin 3) :
    slotExponent j a (l, k) = if l = j ∧ a.val = k.val + 1 then 1 else 0 := by
  by_cases h0 : a.val = 0
  · simp only [slotExponent, dite_eq_left h0, Finsupp.zero_apply]
    rw [ite_eq_right (by omega)]
  · simp only [slotExponent, dite_eq_right h0, Finsupp.single_apply]
    congr 1
    simp only [Prod.mk.injEq, Fin.ext_iff]
    apply propext
    omega

@[simp] theorem pauliExponent_apply (J : Finset (Fin 20)) (a : J → Fin 4)
    (j : J) (k : Fin 3) :
    pauliExponent J a (j.val, k) = if (a j).val = k.val + 1 then 1 else 0 := by
  simp [pauliExponent]

theorem pauliExponent_injective (J : Finset (Fin 20)) :
    Function.Injective (pauliExponent J) := by
  intro a b h
  funext j
  have he (k : Fin 3) := congrArg (fun m : (Fin 20 × Fin 3) →₀ ℕ => m (j.val, k)) h
  simp only [pauliExponent_apply] at he
  have h0 := he 0
  have h1 := he 1
  have h2 := he 2
  generalize ha : a j = aa at *
  generalize hb : b j = bb at *
  fin_cases aa <;> fin_cases bb <;> norm_num at *

theorem sum_slotExponent (J : Finset (Fin 20)) (a : J → Fin 4) :
    (∑ j : J, slotExponent j.val (a j)) = pauliExponent J a := by
  classical
  ext ⟨l, k⟩
  simp only [Finsupp.finsetSum_apply, slotExponent_apply]
  by_cases hv : l ∈ J
  · let j : J := ⟨l, hv⟩
    rw [Finset.sum_eq_single j]
    · simpa only [j, eq_self, true_and] using (pauliExponent_apply J a j k).symm
    · intro q _ hq
      have hneq : l ≠ q.val := by intro h; exact hq (Subtype.ext h.symm)
      simp [hneq]
    · simp
  · rw [Finset.sum_eq_zero]
    · simp [pauliExponent, hv]
    · intro q _
      have hneq : l ≠ q.val := by intro h; exact hv (h ▸ q.property)
      simp [hneq]

def slotPolynomial (j : Fin 20) (b : Fin 4 → ℝ) : RealPoly :=
  ∑ a : Fin 4, MvPolynomial.monomial (slotExponent j a) (b a)

theorem prod_slotPolynomial (J : Finset (Fin 20)) (b : J → Fin 4 → ℝ) :
    (∏ j : J, slotPolynomial j.val (b j)) =
      ∑ a : J → Fin 4, MvPolynomial.monomial (pauliExponent J a) (∏ j, b j (a j)) := by
  classical
  simp only [slotPolynomial, Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [← MvPolynomial.monomial_sum_prod, sum_slotExponent]

theorem realPauliOperator_sum (J : Finset (Fin 20)) {α : Type*} (s : Finset α)
    (p : α → RealPoly) :
    realPauliOperator J (∑ a ∈ s, p a) = ∑ a ∈ s, realPauliOperator J (p a) := by
  classical
  ext σ τ
  simp only [realPauliOperator, MvPolynomial.coeff_sum, Complex.ofReal_sum, Finset.sum_mul,
    Matrix.sum_apply]
  rw [Finset.sum_comm]

theorem realPauliOperator_C_mul (J : Finset (Fin 20)) (c : ℝ) (p : RealPoly) :
    realPauliOperator J (MvPolynomial.C c * p) = (c : ℂ) • realPauliOperator J p := by
  ext σ τ
  simp only [realPauliOperator, MvPolynomial.coeff_C_mul, Complex.ofReal_mul,
    Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem realPauliOperator_monomial (J : Finset (Fin 20)) (a : J → Fin 4) (c : ℝ) :
    realPauliOperator J (MvPolynomial.monomial (pauliExponent J a) c) =
      (c : ℂ) • tensorMatrix J (fun j => pauli (a j)) := by
  classical
  ext σ τ
  simp only [realPauliOperator, MvPolynomial.coeff_monomial,
    (pauliExponent_injective J).eq_iff, tensorMatrix, Matrix.smul_apply, smul_eq_mul]
  simp [apply_ite]

theorem realPauliOperator_prod (J : Finset (Fin 20)) (b : J → Fin 4 → ℝ) :
    realPauliOperator J (∏ j : J, slotPolynomial j.val (b j)) =
      tensorMatrix J (fun j => ∑ a : Fin 4, (b j a : ℂ) • pauli a) := by
  classical
  rw [prod_slotPolynomial, realPauliOperator_sum]
  simp only [realPauliOperator_monomial]
  ext σ τ
  simp only [tensorMatrix, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Complex.ofReal_prod, ← Finset.prod_mul_distrib, Fintype.prod_sum]

/-- The local affine vector factor, with constant coefficient one. -/
def affineSlot (j : Fin 20) (n : Vec3) : RealPoly :=
  1 + ∑ k : Fin 3, MvPolynomial.C (n k) * MvPolynomial.X (j, k)

theorem affineSlot_eq (j : Fin 20) (n : Vec3) :
    affineSlot j n = slotPolynomial j (pauliCoordinate n) := by
  simp [affineSlot, slotPolynomial, Fin.sum_univ_succ, slotExponent,
    pauliCoordinate, MvPolynomial.X, MvPolynomial.C_mul_monomial]

theorem pauliCoordinate_matrix (n : Vec3) :
    (∑ a : Fin 4, (pauliCoordinate n a : ℂ) • pauli a) = 1 + blochMatrix n := by
  simp [Fin.sum_univ_succ, pauliCoordinate, blochMatrix, pauli]

theorem realPauliOperator_affine_prod (J : Finset (Fin 20)) (n : J → Vec3) :
    realPauliOperator J (∏ j : J, affineSlot j.val (n j)) =
      tensorMatrix J (fun j => 1 + blochMatrix (n j)) := by
  simp_rw [affineSlot_eq, realPauliOperator_prod, pauliCoordinate_matrix]

end AKLT.W.H1M052
