import AKLT.Blueprint.H1.NodesSector

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.H1M035

private theorem tokenMatrix_conjTranspose (J : Finset (Fin 20)) (j : J)
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (tokenMatrix J j A).conjTranspose = tokenMatrix J j A.conjTranspose := by
  classical
  ext σ τ
  simp only [Matrix.conjTranspose_apply, tokenMatrix]
  have hiff : (∀ k, k ≠ j → τ k = σ k) ↔ (∀ k, k ≠ j → σ k = τ k) := by
    constructor <;> intro h k hk <;> exact (h k hk).symm
  by_cases h : ∀ k, k ≠ j → σ k = τ k
  · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
  · rw [ite_eq_right (mt hiff.mp h), ite_eq_right h]
    simp

private theorem pauliZ_conjTranspose : (pauli 3).conjTranspose = pauli 3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [pauli, Matrix.conjTranspose_apply]

private theorem pauliPlus_conjTranspose :
    (pauli 1 + Complex.I • pauli 2).conjTranspose =
      pauli 1 - Complex.I • pauli 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauli, Matrix.conjTranspose_apply, Complex.conj_I]

private theorem sum_tokenMatrix_conjTranspose (J : Finset (Fin 20))
    (A B : Matrix (Fin 2) (Fin 2) ℂ) (h : A.conjTranspose = B) :
    (∑ j : J, tokenMatrix J j A).conjTranspose = ∑ j : J, tokenMatrix J j B := by
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [tokenMatrix_conjTranspose, h]

private theorem totalSpinZ_adjoint (J : Finset (Fin 20)) :
    (totalSpinZ J).adjoint = totalSpinZ J := by
  unfold totalSpinZ
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  congr 1
  rw [Matrix.conjTranspose_smul, sum_tokenMatrix_conjTranspose J _ _ pauliZ_conjTranspose]
  simp

private theorem totalSpinPlus_adjoint (J : Finset (Fin 20)) :
    (totalSpinPlus J).adjoint = totalSpinMinus J := by
  unfold totalSpinPlus totalSpinMinus
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  congr 1
  rw [Matrix.conjTranspose_smul,
    sum_tokenMatrix_conjTranspose J _ _ pauliPlus_conjTranspose]
  simp

theorem main : AKLT.Blueprint.H1.SpinAdjointStatement := by
  intro J ψ χ
  constructor
  · calc
      inner ℂ (totalSpinZ J ψ) χ = inner ℂ ψ ((totalSpinZ J).adjoint χ) :=
        (LinearMap.adjoint_inner_right (totalSpinZ J) ψ χ).symm
      _ = inner ℂ ψ (totalSpinZ J χ) := by rw [totalSpinZ_adjoint]
  · calc
      inner ℂ (totalSpinPlus J ψ) χ = inner ℂ ψ ((totalSpinPlus J).adjoint χ) :=
        (LinearMap.adjoint_inner_right (totalSpinPlus J) ψ χ).symm
      _ = inner ℂ ψ (totalSpinMinus J χ) := by rw [totalSpinPlus_adjoint]

end AKLT.W.H1M035

#print axioms AKLT.W.H1M035.main
