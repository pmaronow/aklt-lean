import AKLT.Blueprint.H1.NodesPauli

noncomputable section
open scoped MatrixOrder ComplexOrder

namespace AKLT.W.H1M022

/-- The trace of a product of two positive semidefinite matrices has
nonnegative real part. -/
theorem main : AKLT.Blueprint.H1.TraceProductPositiveStatement := by
  intro n instF instD A B hA hB
  have hA_nonneg : (0 : Matrix n n ℂ) ≤ A := hA.nonneg
  obtain ⟨R, hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA_nonneg
  have hRB : (R * B * star R).PosSemidef := hB.mul_mul_conjTranspose_same R
  have htrace : (A * B).trace = (R * B * star R).trace := by
    rw [hR]
    rw [show (star R * R) * B = star R * R * B by rfl]
    exact (Matrix.trace_mul_cycle R B (star R)).symm
  have hcomplex : 0 ≤ (A * B).trace := by
    rw [htrace]
    exact hRB.trace_nonneg
  exact (RCLike.nonneg_iff.mp hcomplex).1

end AKLT.W.H1M022
