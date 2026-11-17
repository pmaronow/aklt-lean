module
public import AKLT.Blueprint.H1.NodesV2Pauli
public import Mathlib.Analysis.Matrix.Order

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs

namespace AKLT.W.H1M059

private theorem productKernel_posSemidef
    {ι α β : Type*} [Fintype α] [DecidableEq α]
    (S : Finset ι) (coord : ι → α → β)
    (A : ι → Matrix β β ℂ)
    (hA : ∀ i ∈ S, (A i).PosSemidef) :
    Matrix.PosSemidef (fun x y : α => Finset.prod S (fun i => A i (coord i x) (coord i y))) := by
  classical
  revert hA
  induction S using Finset.induction_on with
  | empty =>
      intro hA
      change Matrix.PosSemidef (fun _ _ : α => (1 : ℂ))
      have heq : (fun _ _ : α => (1 : ℂ)) =
          Matrix.vecMulVec (fun _ : α => (1 : ℂ)) (star fun _ : α => (1 : ℂ)) := by
        ext x y
        simp [Matrix.vecMulVec]
      rw [heq]
      exact Matrix.posSemidef_vecMulVec_self_star (fun _ : α => (1 : ℂ))
  | @insert i S hi ih =>
      intro hA
      have hLocal :
          Matrix.PosSemidef (fun x y : α => A i (coord i x) (coord i y)) := by
        change Matrix.PosSemidef ((A i).submatrix (coord i) (coord i))
        exact (hA i (Finset.mem_insert_self i S)).submatrix (coord i)
      have hRest :
          Matrix.PosSemidef (fun x y : α => Finset.prod S
            (fun j => A j (coord j x) (coord j y))) := by
        apply ih
        intro j hj
        exact hA j (Finset.mem_insert_of_mem hj)
      have hEq :
          (fun x y : α => Finset.prod (insert i S)
            (fun k => A k (coord k x) (coord k y))) =
          Matrix.hadamard (fun x y : α => A i (coord i x) (coord i y))
            (fun x y : α => Finset.prod S (fun j => A j (coord j x) (coord j y))) := by
        funext x y
        simp [Finset.prod_insert, hi, Matrix.hadamard]
      rw [hEq]
      exact hLocal.hadamard hRest

theorem main : AKLT.Blueprint.H1.ProductDensityPositiveStatementV2 := by
  intro n J u hLocal
  classical
  let A : J → Matrix (Fin 2) (Fin 2) ℂ := fun j => spinDensity (u j.1)
  have h := productKernel_posSemidef (ι := J) (α := J → Fin 2) (β := Fin 2)
    Finset.univ (fun j σ => σ j) A (by
      intro j hj
      exact hLocal j.1 j.2)
  have hEq : productDensityReal J u =
      (fun x y : J → Fin 2 => Finset.prod J.attach
        (fun j => spinDensity (u j.1) (x j) (y j))) := by
    ext x y
    simp [productDensityReal, Finset.univ_eq_attach]
  rw [hEq]
  exact h

end AKLT.W.H1M059
