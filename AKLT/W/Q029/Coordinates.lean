import AKLT.Blueprint.Q.NodesSplits

noncomputable section
open scoped BigOperators
open AKLT.Blueprint.Q AKLT.Challenge

namespace AKLT.W.Q029

abbrev Pair := PairHilbert

def binomRoot (j : Fin 5) : ℂ := (Real.sqrt (Nat.choose 4 j.val : ℝ) : ℂ)

def diagonalAdjointVector (m : ℕ) : Pair := WithLp.toLp 2 fun p : Fin 5 × Fin 5 =>
  if p.1.val + p.2.val = m then binomRoot p.1 * binomRoot p.2 else 0

def pairZ : Module.End ℂ Pair := pairAt spinZ 0 + pairAt spinZ 1

theorem pairAt_left_apply (A : Matrix (Fin 5) (Fin 5) ℂ) (v : Pair) (p : Fin 5 × Fin 5) :
    ((pairAt A 0 v).ofLp) p = ∑ i : Fin 5, A p.1 i * v (i,p.2) := by
  let M : Matrix (Fin 5 × Fin 5) (Fin 5 × Fin 5) ℂ := fun σ τ => if σ.2 = τ.2 then A σ.1 τ.1 else 0
  change (WithLp.ofLp (Matrix.toLpLin 2 2 M v)) p = _
  rw [Matrix.ofLp_toLpLin, Matrix.toLin'_apply, Matrix.mulVec_apply]
  simp [dotProduct, Matrix.row, M, Fintype.sum_prod_type]

lemma pairAt_right_apply (A : Matrix (Fin 5) (Fin 5) ℂ) (v : Pair) (p : Fin 5 × Fin 5) :
    ((pairAt A 1 v).ofLp) p = ∑ i : Fin 5, A p.2 i * v (p.1,i) := by
  let M : Matrix (Fin 5 × Fin 5) (Fin 5 × Fin 5) ℂ := fun σ τ => if σ.1 = τ.1 then A σ.2 τ.2 else 0
  change (WithLp.ofLp (Matrix.toLpLin 2 2 M v)) p = _
  rw [Matrix.ofLp_toLpLin, Matrix.toLin'_apply, Matrix.mulVec_apply]
  simp [dotProduct, Matrix.row, M, Fintype.sum_prod_type]

lemma sum_filter_left (j k : Fin 5) (m : ℕ) (f : Fin 5 → ℂ) :
    (∑ i : Fin 5, if i.val + k.val = m then if j = i then f i else 0 else 0) =
      if j.val + k.val = m then f j else 0 := by
  classical
  rw [Fintype.sum_eq_single j]
  · by_cases h : j.val + k.val = m <;> simp [h]
  · intro i hi
    simp [Ne.symm hi]

lemma sum_filter_right (j k : Fin 5) (m : ℕ) (f : Fin 5 → ℂ) :
    (∑ i : Fin 5, if j.val + i.val = m then if k = i then f i else 0 else 0) =
      if j.val + k.val = m then f k else 0 := by
  classical
  rw [Fintype.sum_eq_single k]
  · by_cases h : j.val + k.val = m <;> simp [h]
  · intro i hi
    simp [Ne.symm hi]

lemma pairZ_on_diag (m : Fin 9) : pairZ (diagonalAdjointVector m.val) =
    ((4 : ℂ) - (m.val : ℂ)) • diagonalAdjointVector m.val := by
  ext p
  rcases p with ⟨j,k⟩
  simp only [pairZ, WithLp.ofLp_add, Pi.add_apply, LinearMap.add_apply,
    pairAt_left_apply, pairAt_right_apply]
  simp [spinZ, diagonalAdjointVector, binomRoot, sum_filter_left,
    sum_filter_right]
  split_ifs with h
  · have hc : (j.val : ℂ) + (k.val : ℂ) = (m.val : ℂ) := by exact_mod_cast h
    rw [← hc]
    ring
  · simp

end AKLT.W.Q029
