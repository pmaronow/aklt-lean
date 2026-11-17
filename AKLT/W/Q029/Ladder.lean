module
public import AKLT.W.Q029.Coordinates

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Blueprint.Q AKLT.Challenge

namespace AKLT.W.Q029

def pairU : Module.End ℂ Pair := pairAt spinPlus 0 + pairAt spinPlus 1
def pairD : Module.End ℂ Pair := pairAt spinMinus 0 + pairAt spinMinus 1

private theorem sqrt_six_sq : (Real.sqrt 6 : ℂ) ^ 2 = 6 := by
  norm_cast
  exact Real.sq_sqrt (by norm_num)

private theorem sqrt_six_cube : (Real.sqrt 6 : ℂ) ^ 3 = 6 * (Real.sqrt 6 : ℂ) := by
  rw [pow_succ, sqrt_six_sq]

theorem pairU_zero : pairU (diagonalAdjointVector 0) = 0 := by
  ext ⟨j, k⟩
  simp only [pairU, LinearMap.add_apply, WithLp.ofLp_add, Pi.add_apply,
    pairAt_left_apply, pairAt_right_apply]
  fin_cases j <;> fin_cases k <;>
    norm_num [diagonalAdjointVector, binomRoot, spinPlus, Fin.sum_univ_succ]

set_option maxHeartbeats 2400000 in
theorem pairU_succ (m : Fin 8) : pairU (diagonalAdjointVector (m.val + 1)) =
    ((8 - m.val : ℕ) : ℂ) • diagonalAdjointVector m.val := by
  ext ⟨j, k⟩
  simp only [pairU, LinearMap.add_apply, WithLp.ofLp_add, Pi.add_apply,
    pairAt_left_apply, pairAt_right_apply]
  fin_cases m <;> fin_cases j <;> fin_cases k <;>
    norm_num [diagonalAdjointVector, binomRoot, spinPlus, Fin.sum_univ_succ,
      Nat.choose, -Real.sqrt_mul, -Real.sqrt_mul'] <;>
    ring_nf <;> simp only [sqrt_six_sq, sqrt_six_cube] <;> ring

set_option maxHeartbeats 2400000 in
theorem pairD_on_diag (m : Fin 9) : pairD (diagonalAdjointVector m.val) =
    ((m.val + 1 : ℕ) : ℂ) • diagonalAdjointVector (m.val + 1) := by
  ext ⟨j, k⟩
  simp only [pairD, LinearMap.add_apply, WithLp.ofLp_add, Pi.add_apply,
    pairAt_left_apply, pairAt_right_apply]
  fin_cases m <;> fin_cases j <;> fin_cases k <;>
    norm_num [diagonalAdjointVector, binomRoot, spinMinus, spinPlus,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ, Nat.choose,
      map_ofNat, -Real.sqrt_mul, -Real.sqrt_mul'] <;>
    ring_nf <;> simp only [sqrt_six_sq, sqrt_six_cube] <;> ring

theorem diagonalAdjointVector_nine : diagonalAdjointVector 9 = 0 := by
  ext ⟨j, k⟩
  have h : j.val + k.val ≠ 9 := by have := j.isLt; have := k.isLt; omega
  simp [diagonalAdjointVector, h]

end AKLT.W.Q029
