import AKLT.Blueprint.H1.NodesStructure

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs

namespace AKLT.W.H1M050

private lemma tokenMatrix_smul (J : Finset (Fin 20)) (j : J)
    (c : ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    tokenMatrix J j (c • A) = c • tokenMatrix J j A := by
  ext σ τ
  simp [tokenMatrix]

private lemma tokenMatrix_add (J : Finset (Fin 20)) (j : J)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    tokenMatrix J j (A + B) = tokenMatrix J j A + tokenMatrix J j B := by
  ext σ τ
  change (if ∀ k : J, k ≠ j → σ k = τ k then
      (A + B) (σ j) (τ j) else 0) =
    (if ∀ k : J, k ≠ j → σ k = τ k then A (σ j) (τ j) else 0) +
      (if ∀ k : J, k ≠ j → σ k = τ k then B (σ j) (τ j) else 0)
  split_ifs <;> simp

private lemma sum_tokenMatrix_smul (J : Finset (Fin 20)) (c : ℂ)
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (∑ j : J, tokenMatrix J j (c • A)) = c • ∑ j : J, tokenMatrix J j A := by
  simp only [tokenMatrix_smul, Finset.smul_sum]

private lemma sum_tokenMatrix_add (J : Finset (Fin 20))
    (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    (∑ j : J, tokenMatrix J j (A + B)) =
      (∑ j : J, tokenMatrix J j A) + ∑ j : J, tokenMatrix J j B := by
  simp only [tokenMatrix_add, Finset.sum_add_distrib]

private lemma toEuclideanLin_mul {J : Type*} [Fintype J] [DecidableEq J]
    (A B : Matrix J J ℂ) :
    Matrix.toEuclideanLin (A * B) =
      (Matrix.toEuclideanLin A) * (Matrix.toEuclideanLin B) := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  simp only [Module.End.mul_eq_comp]
  exact Matrix.toLin_mul _ _ _ A B

private lemma commute_toEuclideanLin {J : Type*} [Fintype J] [DecidableEq J]
    (A B : Matrix J J ℂ) (h : Commute A B) :
    Commute (Matrix.toEuclideanLin A) (Matrix.toEuclideanLin B) := by
  change A * B = B * A at h
  change (Matrix.toEuclideanLin A) * (Matrix.toEuclideanLin B) =
    (Matrix.toEuclideanLin B) * (Matrix.toEuclideanLin A)
  rw [← toEuclideanLin_mul, ← toEuclideanLin_mul]
  exact congrArg Matrix.toEuclideanLin h

private lemma commute_cancel_smul {J : Type*} [Fintype J] [DecidableEq J]
    (a b : Matrix J J ℂ) (c : ℂ) (hc : c ≠ 0) (h : Commute a (c • b)) : Commute a b := by
  have h' := h.smul_right c⁻¹
  simpa [smul_smul, hc] using h'

theorem main : AKLT.Blueprint.H1.SpinGeneratorTransferStatement := by
  intro J M h
  let S (k : Fin 3) : Matrix (J → Fin 2) (J → Fin 2) ℂ :=
    ∑ j : J, tokenMatrix J j (pauli ⟨k.val + 1, by omega⟩)
  have hS (k : Fin 3) : Commute M (S k) := by
    have hk := h k
    change Commute M (∑ j : J,
      tokenMatrix J j ((-Complex.I) • pauli ⟨k.val + 1, by omega⟩)) at hk
    rw [sum_tokenMatrix_smul] at hk
    exact commute_cancel_smul M (S k) (-Complex.I) (by simp) hk
  have hZ : Commute (Matrix.toEuclideanLin M) (AKLT.Defs.totalSpinZ J) := by
    have hk := commute_toEuclideanLin M (S ⟨2, by omega⟩) (hS ⟨2, by omega⟩)
    simpa [AKLT.Defs.totalSpinZ, S] using hk.smul_right (1 / 2 : ℂ)
  have hPlusMatrix : Commute M
      (∑ j : J, tokenMatrix J j (pauli 1 + Complex.I • pauli 2)) := by
    rw [sum_tokenMatrix_add, sum_tokenMatrix_smul]
    exact Commute.add_right (hS ⟨0, by omega⟩) ((hS ⟨1, by omega⟩).smul_right Complex.I)
  have hPlus : Commute (Matrix.toEuclideanLin M) (AKLT.Defs.totalSpinPlus J) := by
    have hp := commute_toEuclideanLin M
      (∑ j : J, tokenMatrix J j (pauli 1 + Complex.I • pauli 2)) hPlusMatrix
    simpa [AKLT.Defs.totalSpinPlus] using hp.smul_right (1 / 2 : ℂ)
  have hMinusMatrix : Commute M
      (∑ j : J, tokenMatrix J j (pauli 1 - Complex.I • pauli 2)) := by
    rw [show pauli 1 - Complex.I • pauli 2 = pauli 1 + (-Complex.I) • pauli 2 by module]
    rw [sum_tokenMatrix_add, sum_tokenMatrix_smul]
    exact Commute.add_right (hS ⟨0, by omega⟩)
      ((hS ⟨1, by omega⟩).smul_right (-Complex.I))
  have hMinus : Commute (Matrix.toEuclideanLin M) (AKLT.Defs.totalSpinMinus J) := by
    have hm := commute_toEuclideanLin M
      (∑ j : J, tokenMatrix J j (pauli 1 - Complex.I • pauli 2)) hMinusMatrix
    simpa [AKLT.Defs.totalSpinMinus] using hm.smul_right (1 / 2 : ℂ)
  exact ⟨hZ, hPlus, hMinus⟩

end AKLT.W.H1M050

#print axioms AKLT.W.H1M050.main
