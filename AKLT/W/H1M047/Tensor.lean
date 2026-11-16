import AKLT.W.H1M047.Basic

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.H1

namespace AKLT.W.H1M047

/-- A tensor whose two-dimensional factor can depend on the slot. -/
def slotTensor (J : Finset (Fin 20)) (A : J → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (J → Fin 2) (J → Fin 2) ℂ :=
  fun σ τ => ∏ j : J, A j (σ j) (τ j)

lemma slotTensor_mul (J : Finset (Fin 20))
    (A B : J → Matrix (Fin 2) (Fin 2) ℂ) :
    slotTensor J A * slotTensor J B = slotTensor J (fun j => A j * B j) := by
  classical
  ext σ τ
  simp only [slotTensor, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro f _
  exact (Finset.prod_mul_distrib).symm

lemma pauliOperator_eq_sum (J : Finset (Fin 20)) (p : VectorPolynomial) :
    pauliOperator J p = ∑ a : J → Fin 4,
      (p.coeff (pauliExponent J a) : ℂ) • slotTensor J (fun j => pauli (a j)) := by
  ext σ τ
  simp only [pauliOperator, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, slotTensor]

lemma pauli_conjugation_all (g : Matrix (Fin 2) (Fin 2) ℂ)
    (hg : g.conjTranspose * g = 1) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hc : ∀ j : Fin 3, g * pauli ⟨j.val + 1, by omega⟩ * g.conjTranspose =
      ∑ l : Fin 3, (R l j : ℂ) • pauli ⟨l.val + 1, by omega⟩)
    (a : Fin 4) :
    g * pauli a * g.conjTranspose =
      ∑ b : Fin 4, (pauliRotationCoefficient R b a : ℂ) • pauli b := by
  have hg' : g * g.conjTranspose = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (Fin 2))).mp hg
  fin_cases a
  · simp [pauliRotationCoefficient, pauli, hg']
  · simpa [pauliRotationCoefficient, Fin.sum_univ_succ] using hc 0
  · simpa [pauliRotationCoefficient, Fin.sum_univ_succ] using hc 1
  · simpa [pauliRotationCoefficient, Fin.sum_univ_succ] using hc 2

lemma slotTensor_pauli_rotation (J : Finset (Fin 20))
    (R : Matrix (Fin 3) (Fin 3) ℝ) (a : J → Fin 4) :
    slotTensor J (fun j => ∑ b : Fin 4,
        (pauliRotationCoefficient R b (a j) : ℂ) • pauli b) =
      ∑ b : J → Fin 4, (∏ j : J, (pauliRotationCoefficient R (b j) (a j) : ℂ)) •
        slotTensor J (fun j => pauli (b j)) := by
  classical
  ext σ τ
  simp only [slotTensor, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro b _
  exact Finset.prod_mul_distrib

lemma pauli_rotation_expansion (J : Finset (Fin 20)) (p : VectorPolynomial)
    (g : Matrix (Fin 2) (Fin 2) ℂ) (hg : g.conjTranspose * g = 1)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hc : ∀ j : Fin 3, g * pauli ⟨j.val + 1, by omega⟩ * g.conjTranspose =
      ∑ l : Fin 3, (R l j : ℂ) • pauli ⟨l.val + 1, by omega⟩) :
    tensorPowerMatrix J g * pauliOperator J p * (tensorPowerMatrix J g).conjTranspose =
      rotatedPauliOperator J p R := by
  classical
  rw [pauliOperator_eq_sum, tensorPower_conjTranspose, Finset.mul_sum, Finset.sum_mul]
  simp only [mul_smul_comm, smul_mul_assoc]
  change (∑ a : J → Fin 4, (p.coeff (pauliExponent J a) : ℂ) •
    (slotTensor J (fun _ => g) * slotTensor J (fun j => pauli (a j)) *
      slotTensor J (fun _ => g.conjTranspose))) = _
  simp_rw [slotTensor_mul, pauli_conjugation_all g hg R hc, slotTensor_pauli_rotation,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  ext σ τ
  simp only [rotatedPauliOperator, rotatedPauliCoefficient, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Finset.sum_mul, slotTensor]

end AKLT.W.H1M047
