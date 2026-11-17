import AKLT.Blueprint.Win.NodesTopology

noncomputable section

open AKLT.Defs AKLT.Blueprint.Win

namespace AKLT.W.WIN013

theorem main : AKLT.Blueprint.Win.ChainBoxStatement := by
  classical
  intro c
  let vertices : Finset Plane := c.support.biUnion fun e => e.toFinset
  let coordinateBound : Plane → ℕ := fun x => max x.1.natAbs x.2.natAbs
  let M : ℕ := vertices.sup coordinateBound
  let R : ℤ := (max 1 M : ℕ)
  refine ⟨R, ?_, ?_⟩
  · change (1 : ℤ) ≤ (max 1 M : ℕ)
    exact_mod_cast (Nat.le_max_left 1 M)
  · intro e he x hx
    have hxv : x ∈ vertices := by
      change x ∈ c.support.biUnion (fun e => e.toFinset)
      exact Finset.mem_biUnion.mpr ⟨e, he, Sym2.mem_toFinset.mpr hx⟩
    have hcoord : coordinateBound x ≤ M := by
      exact Finset.le_sup hxv
    have h1 : x.1.natAbs ≤ max 1 M :=
      le_trans (Nat.le_max_left _ _) (le_trans hcoord (Nat.le_max_right _ _))
    have h2 : x.2.natAbs ≤ max 1 M :=
      le_trans (Nat.le_max_right _ _) (le_trans hcoord (Nat.le_max_right _ _))
    constructor
    · unfold R
      rw [Int.abs_eq_natAbs]
      exact_mod_cast h1
    · unfold R
      rw [Int.abs_eq_natAbs]
      exact_mod_cast h2

#print axioms main

end AKLT.W.WIN013
