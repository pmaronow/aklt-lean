module
public import AKLT.W.Q029.Coordinates

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Blueprint.Q AKLT.Challenge

namespace AKLT.W.Q029

def diagonalMonomial (m : ℕ) : MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.X 0 ^ (8 - m) * MvPolynomial.X 1 ^ m

theorem inner_diagonalAdjointVector (m : ℕ) (v : Pair) :
    inner ℂ (diagonalAdjointVector m) v =
      ∑ j : Fin 5, ∑ k : Fin 5,
        if j.val + k.val = m then v (j, k) * binomRoot j * binomRoot k else 0 := by
  simp [PiLp.inner_apply, RCLike.inner_apply, diagonalAdjointVector,
    binomRoot, Fintype.sum_prod_type, apply_ite, mul_assoc]

theorem pairDiagonal_terms (v : Pair) : pairDiagonal v =
    ∑ j : Fin 5, ∑ k : Fin 5,
      MvPolynomial.C (v (j, k) * binomRoot j * binomRoot k) *
        diagonalMonomial (j.val + k.val) := by
  change MvPolynomial.rename Prod.snd (pairPolynomial v) = _
  simp only [pairPolynomial, map_sum, map_mul, map_pow,
    MvPolynomial.rename_C, MvPolynomial.rename_X]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  have h : (4 - j.val) + (4 - k.val) = 8 - (j.val + k.val) := by
    have := j.isLt
    have := k.isLt
    omega
  dsimp only [diagonalMonomial]
  change MvPolynomial.C (v (j, k)) * MvPolynomial.C (binomRoot j) *
      MvPolynomial.C (binomRoot k) * MvPolynomial.X 0 ^ (4 - j.val) *
      MvPolynomial.X 1 ^ j.val * MvPolynomial.X 0 ^ (4 - k.val) *
      MvPolynomial.X 1 ^ k.val = _
  simp only [← MvPolynomial.C_mul]
  let a : MvPolynomial (Fin 2) ℂ :=
    MvPolynomial.C (v (j, k) * binomRoot j * binomRoot k)
  change a * MvPolynomial.X 0 ^ (4 - j.val) * MvPolynomial.X 1 ^ j.val *
    MvPolynomial.X 0 ^ (4 - k.val) * MvPolynomial.X 1 ^ k.val =
    a * (MvPolynomial.X 0 ^ (8 - (j.val + k.val)) *
      MvPolynomial.X 1 ^ (j.val + k.val))
  calc
    _ = a *
        (MvPolynomial.X 0 ^ (4 - j.val) * MvPolynomial.X 0 ^ (4 - k.val)) *
        (MvPolynomial.X 1 ^ j.val * MvPolynomial.X 1 ^ k.val) := by ring
    _ = a * (MvPolynomial.X 0 ^ (8 - (j.val + k.val)) *
        MvPolynomial.X 1 ^ (j.val + k.val)) := by
      rw [← pow_add, ← pow_add, h, mul_assoc]

set_option maxHeartbeats 800000 in
theorem pairDiagonal_expansion (v : Pair) : pairDiagonal v =
    ∑ m : Fin 9, MvPolynomial.C (inner ℂ (diagonalAdjointVector m.val) v) *
      diagonalMonomial m.val := by
  rw [pairDiagonal_terms]
  calc
    _ = ∑ j : Fin 5, ∑ k : Fin 5, ∑ m : Fin 9,
        if j.val + k.val = m.val then
          MvPolynomial.C (v (j, k) * binomRoot j * binomRoot k) *
            diagonalMonomial m.val else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      let m : Fin 9 := ⟨j.val + k.val, by have := j.isLt; have := k.isLt; omega⟩
      rw [Fintype.sum_eq_single m]
      · simp [m]
      · intro n hn
        have h : j.val + k.val ≠ n.val := by
          intro he
          exact hn (Fin.ext he.symm)
        simp [h]
    _ = ∑ m : Fin 9, ∑ j : Fin 5, ∑ k : Fin 5,
        if j.val + k.val = m.val then
          MvPolynomial.C (v (j, k) * binomRoot j * binomRoot k) *
            diagonalMonomial m.val else 0 := by
      conv_lhs =>
        arg 2
        ext j
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
    _ = _ := by
      simp [inner_diagonalAdjointVector, map_sum, Finset.sum_mul,
        apply_ite, ite_mul]

/-- The weighted coefficient vectors contain the kernel complement. -/
theorem pairTopSpan :
    (LinearMap.ker pairDiagonal)ᗮ ≤
      Submodule.span ℂ (Set.range (fun m : Fin 9 => diagonalAdjointVector m.val)) := by
  apply Submodule.orthogonal_le_iff_orthogonal_le.mpr
  intro v hv
  rw [LinearMap.mem_ker, pairDiagonal_expansion]
  apply Finset.sum_eq_zero
  intro m _
  have h : inner ℂ (diagonalAdjointVector m.val) v = 0 :=
    Submodule.inner_right_of_mem_orthogonal
      (Submodule.subset_span (Set.mem_range_self m)) hv
  simp [h]

end AKLT.W.Q029
