module
public import AKLT.Blueprint.Win.NodesCut

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.WIN068

private theorem internalBond_adjacent {B : Finset Plane} {e : Plane × Plane}
    (he : e ∈ internalBonds B) : Adjacent e.1 e.2 := by
  rw [internalBonds, Finset.mem_biUnion] at he
  rcases he with ⟨x, hx, he⟩
  rcases Finset.mem_image.mp he with ⟨y, hy, hxy⟩
  have hp : y ∈ positiveNeighbours x := (Finset.mem_inter.mp hy).1
  cases hxy
  simp [positiveNeighbours] at hp
  rcases hp with hp | hp
  · rw [hp]
    simp [Adjacent, latticeDist]
  · rw [hp]
    simp [Adjacent, latticeDist]

theorem main : AKLT.Blueprint.Win.WindowWeightPositiveStatement := by
  intro hframes κ hκ B s
  rcases hframes with ⟨_, _, hbound, _, _, _, _, hbonds, _⟩
  rw [AKLT.Blueprint.Win.windowWeight]
  apply mul_pos
  · positivity
  · apply Finset.prod_pos
    intro e he
    have hadj : Adjacent e.1 e.2 := internalBond_adjacent he
    have hcol : κ e.1 ≠ κ e.2 := hκ e.1 e.2 hadj
    have hfactor := (hbonds (κ e.1) (κ e.2) hcol
      (extendLetters s e.1) (extendLetters s e.2)).1
    exact lt_of_lt_of_le hbound hfactor

end AKLT.W.WIN068
