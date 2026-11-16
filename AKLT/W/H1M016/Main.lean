import AKLT.Blueprint.H1.NodesPauli

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs
open AKLT.Blueprint.H1

namespace AKLT.W.H1M016

private theorem blochMatrix_entries (u : Vec3) :
    blochMatrix u =
      !![(u 2 : ℂ), (u 0 : ℂ) - Complex.I * u 1;
        (u 0 : ℂ) + Complex.I * u 1, -(u 2 : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blochMatrix, pauli, Fin.sum_univ_succ, Matrix.add_apply] <;> ring

theorem main : AKLT.Blueprint.H1.BlochAlgebraStatement := by
  intro u
  have he := blochMatrix_entries u
  constructor
  · change (blochMatrix u).conjTranspose = blochMatrix u
    rw [he]
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp [Matrix.conjTranspose_apply, Complex.conj_ofReal, Complex.conj_I]
    all_goals ring
  constructor
  · rw [he]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.smul_apply,
        normSq, dot] <;> ring_nf <;>
        simp only [Complex.I_sq] <;> ring
  · rw [he]
    simp [Matrix.trace, Fin.sum_univ_succ]

end AKLT.W.H1M016
