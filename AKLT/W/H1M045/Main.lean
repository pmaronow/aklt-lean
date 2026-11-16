import AKLT.Blueprint.H1.NodesStructure

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.H1M045

private def pauliCoordinates (A : Matrix (Fin 2) (Fin 2) ℂ) (l : Fin 3) : ℝ :=
  if l.val = 0 then (A 0 1).re else
  if l.val = 1 then -(A 0 1).im else (A 0 0).re

private lemma pauli_hermitian (j : Fin 3) :
    (pauli ⟨j.val + 1, by omega⟩).IsHermitian := by
  fin_cases j <;> ext i k <;> fin_cases i <;> fin_cases k <;>
    norm_num [Matrix.IsHermitian, pauli, Matrix.conjTranspose_apply]

private lemma pauli_trace_zero (j : Fin 3) :
    (pauli ⟨j.val + 1, by omega⟩).trace = 0 := by
  fin_cases j <;> norm_num [pauli, Matrix.trace, Fin.sum_univ_succ]

private lemma traceless_hermitian_pauli_expansion
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hH : A.IsHermitian) (htr : A.trace = 0) :
    A = ∑ l : Fin 3, (pauliCoordinates A l : ℂ) • pauli ⟨l.val + 1, by omega⟩ := by
  have hHext := Matrix.IsHermitian.ext_iff.mp hH
  have hdiag : (A 0 0).im = 0 := by
    have h := congrArg Complex.im (hHext 0 0)
    have heq : -(A 0 0).im = (A 0 0).im := by simpa using h
    linarith
  have hoff : star (A 0 1) = A 1 0 := hHext 1 0
  have htr' : A 0 0 + A 1 1 = 0 := by
    simpa [Matrix.trace, Fin.sum_univ_succ] using htr
  have hdiag11 : (A 1 1).im = 0 := by
    have h := congrArg Complex.im htr'
    simpa [hdiag] using h
  have htrRe : (A 0 0).re + (A 1 1).re = 0 := by
    have h := congrArg Complex.re htr'
    simpa using h
  have hoffRe : (A 0 1).re = (A 1 0).re := by
    have h := congrArg Complex.re hoff
    simpa using h
  have hoffIm : (A 1 0).im = -(A 0 1).im := by
    have h := congrArg Complex.im hoff
    have h' : -(A 0 1).im = (A 1 0).im := by simpa using h
    linarith
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext
  all_goals simp [pauliCoordinates, pauli, Matrix.sum_apply, Matrix.smul_apply,
    Fin.sum_univ_succ, hdiag, hdiag11]
  all_goals linarith [htrRe, hoffRe, hoffIm]

private lemma conjugate_pauli_hermitian (g : Matrix (Fin 2) (Fin 2) ℂ)
    (j : Fin 3) :
    (g * pauli ⟨j.val + 1, by omega⟩ * g.conjTranspose).IsHermitian := by
  rw [Matrix.IsHermitian]
  calc
    (g * pauli ⟨j.val + 1, by omega⟩ * g.conjTranspose).conjTranspose =
        (g.conjTranspose).conjTranspose *
          (pauli ⟨j.val + 1, by omega⟩).conjTranspose * g.conjTranspose := by
            simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = g * pauli ⟨j.val + 1, by omega⟩ * g.conjTranspose := by
          have hp := pauli_hermitian j
          change (pauli ⟨j.val + 1, by omega⟩).conjTranspose =
            pauli ⟨j.val + 1, by omega⟩ at hp
          simp only [Matrix.conjTranspose_conjTranspose, hp, Matrix.mul_assoc]

private lemma conjugate_pauli_trace_zero (g : Matrix (Fin 2) (Fin 2) ℂ)
    (hu : g.conjTranspose * g = 1) (j : Fin 3) :
    (g * pauli ⟨j.val + 1, by omega⟩ * g.conjTranspose).trace = 0 := by
  calc
    Matrix.trace (g * pauli ⟨j.val + 1, by omega⟩ * g.conjTranspose) =
        Matrix.trace (g.conjTranspose * (g * pauli ⟨j.val + 1, by omega⟩)) := by
          rw [Matrix.trace_mul_comm]
    _ = Matrix.trace ((g.conjTranspose * g) * pauli ⟨j.val + 1, by omega⟩) := by
          rw [← Matrix.mul_assoc]
    _ = Matrix.trace (pauli ⟨j.val + 1, by omega⟩) := by rw [hu, Matrix.one_mul]
    _ = 0 := pauli_trace_zero j

theorem main : AKLT.Blueprint.H1.AdjointPauliCoordinatesStatement := by
  intro g hu hdet
  let R : Matrix (Fin 3) (Fin 3) ℝ := fun l j =>
    pauliCoordinates (g * pauli ⟨j.val + 1, by omega⟩ * g.conjTranspose) l
  refine ⟨R, ?_⟩
  intro j
  change g * pauli ⟨j.val + 1, by omega⟩ * g.conjTranspose =
    ∑ l : Fin 3, (R l j : ℂ) • pauli ⟨l.val + 1, by omega⟩
  exact traceless_hermitian_pauli_expansion _
    (conjugate_pauli_hermitian g j) (conjugate_pauli_trace_zero g hu j)

end AKLT.W.H1M045

