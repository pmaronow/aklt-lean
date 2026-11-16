import AKLT.Blueprint.H1.NodesStructure

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.H1M046

private def σ (j : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  pauli ⟨j.val + 1, by omega⟩

private theorem pauli_trace_product (j k : Fin 3) :
    Matrix.trace (σ j * σ k) = if j = k then (2 : ℂ) else 0 := by
  fin_cases j <;> fin_cases k <;>
    simp [σ, pauli, Matrix.trace, Fin.sum_univ_succ] <;> norm_num

private theorem trace_conjugate (g A : Matrix (Fin 2) (Fin 2) ℂ)
    (hg : g.conjTranspose * g = 1) :
    Matrix.trace (g * A * g.conjTranspose) = Matrix.trace A := by
  calc
    Matrix.trace (g * A * g.conjTranspose) =
        Matrix.trace (g.conjTranspose * g * A) := by
          rw [Matrix.trace_mul_cycle]
    _ = Matrix.trace A := by rw [hg]; simp

private theorem conjugated_product (g : Matrix (Fin 2) (Fin 2) ℂ)
    (hg : g.conjTranspose * g = 1) (j k : Fin 3) :
    (g * σ j * g.conjTranspose) * (g * σ k * g.conjTranspose) =
      g * (σ j * σ k) * g.conjTranspose := by
  calc
    (g * σ j * g.conjTranspose) * (g * σ k * g.conjTranspose) =
        g * (σ j * (g.conjTranspose * g) * σ k) * g.conjTranspose := by
          simp only [Matrix.mul_assoc]
    _ = g * (σ j * 1 * σ k) * g.conjTranspose := by rw [hg]
    _ = g * (σ j * σ k) * g.conjTranspose := by simp

private theorem coordinate_trace (R : Matrix (Fin 3) (Fin 3) ℝ) (j k : Fin 3) :
    Matrix.trace
      ((∑ l : Fin 3, (R l j : ℂ) • σ l) *
       (∑ l : Fin 3, (R l k : ℂ) • σ l)) =
      ∑ l : Fin 3, (R l j : ℂ) * (R l k : ℂ) * 2 := by
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_sum, Matrix.trace_smul]
  simp [pauli_trace_product, mul_assoc, mul_left_comm]

theorem main : AKLT.Blueprint.H1.AdjointPauliOrthogonalStatement := by
  intro g hg R hcoord
  apply Matrix.ext
  intro j k
  have hconj : Matrix.trace
      ((g * σ j * g.conjTranspose) * (g * σ k * g.conjTranspose)) =
      Matrix.trace (σ j * σ k) := by
    rw [conjugated_product g hg j k]
    exact trace_conjugate g (σ j * σ k) hg
  have hcoordTrace : Matrix.trace
      ((∑ l : Fin 3, (R l j : ℂ) • σ l) *
       (∑ l : Fin 3, (R l k : ℂ) • σ l)) =
      ∑ l : Fin 3, (R l j : ℂ) * (R l k : ℂ) * 2 :=
    coordinate_trace R j k
  have hsum : (R.transpose * R) j k = ∑ l : Fin 3, R l j * R l k := by
    simp [Matrix.mul_apply, Matrix.transpose_apply]
  change (R.transpose * R) j k = if j = k then 1 else 0
  have htr : (2 : ℂ) * ((R.transpose * R) j k : ℂ) =
      if j = k then (2 : ℂ) else 0 := by
    have hleft : Matrix.trace
        ((∑ l : Fin 3, (R l j : ℂ) • σ l) *
         (∑ l : Fin 3, (R l k : ℂ) • σ l)) =
        Matrix.trace (σ j * σ k) := by
      simpa only [σ, hcoord j, hcoord k] using hconj
    rw [hcoordTrace, pauli_trace_product] at hleft
    have hcast : (∑ l : Fin 3, (R l j : ℂ) * (R l k : ℂ) * 2) =
        (2 : ℂ) * (((∑ l : Fin 3, R l j * R l k : ℝ)) : ℂ) := by
      simp [Finset.mul_sum, mul_assoc, mul_comm]
    rw [hcast] at hleft
    rw [hsum]
    exact hleft
  rcases eq_or_ne j k with hEq | hNe
  · subst k
    have hx : ((R.transpose * R) j j : ℂ) = 1 := by
      apply (mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0))
      simpa using htr
    have hreal : (R.transpose * R) j j = 1 := by exact_mod_cast hx
    simpa using hreal
  · have hx : ((R.transpose * R) j k : ℂ) = 0 := by
      have hx' : (2 : ℂ) * ((R.transpose * R) j k : ℂ) = 0 := by
        simpa [hNe] using htr
      exact (mul_eq_zero.mp hx').resolve_left (by norm_num)
    simpa [hNe] using (show (R.transpose * R) j k = 0 by exact_mod_cast hx)

end AKLT.W.H1M046
