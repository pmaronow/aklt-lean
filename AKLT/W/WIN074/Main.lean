module
public import AKLT.Blueprint.Win.NodesCut

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.WIN074

private theorem internalBonds_adjacent {F : Finset Plane} {e : Plane × Plane}
    (he : e ∈ internalBonds F) : Adjacent e.1 e.2 := by
  classical
  rcases e with ⟨ex, ey⟩
  simp only [internalBonds, Finset.mem_biUnion] at he
  obtain ⟨x, hx, he⟩ := he
  simp only [Finset.mem_image] at he
  obtain ⟨y, hy, he⟩ := he
  have hy' : y ∈ positiveNeighbours x := (Finset.mem_inter.mp hy).1
  simp only [Prod.mk.injEq] at he
  rcases he with ⟨rfl, rfl⟩
  simp only [positiveNeighbours, Finset.mem_insert, Finset.mem_singleton] at hy'
  rcases hy' with hy' | hy'
  · rw [hy']
    simp [Adjacent, latticeDist]
  · rw [hy']
    simp [Adjacent, latticeDist]

private theorem originalLegs_adjacent {F : Finset Plane} {e : Plane × Plane}
    (he : e ∈ originalLegs F) : Adjacent e.1 e.2 := by
  classical
  rcases e with ⟨ex, ey⟩
  simp only [originalLegs, Finset.mem_biUnion] at he
  obtain ⟨x, hx, he⟩ := he
  simp only [Finset.mem_image] at he
  obtain ⟨y, hy, he⟩ := he
  have hy' : y ∈ neighbours x := (Finset.mem_sdiff.mp hy).1
  simp only [Prod.mk.injEq] at he
  rcases he with ⟨rfl, rfl⟩
  simp only [neighbours, Finset.mem_image, Finset.mem_univ, true_and] at hy'
  obtain ⟨d, rfl⟩ := hy'
  cases d <;> simp [Adjacent, latticeDist, Compass.step]

theorem main : AKLT.Blueprint.Win.FrameWeightPositiveStatement := by
  intro hFrames κ hκ F η σ
  rcases hFrames with ⟨_, _, hBoundPos, _, _, _, _, hBounds, _⟩
  unfold planeWeight
  apply mul_pos
  · apply mul_pos
    · positivity
    · apply Finset.prod_pos
      intro e he
      have hcol : κ e.1 ≠ κ e.2 := hκ e.1 e.2 (internalBonds_adjacent he)
      have hlower := hBounds (κ e.1) (κ e.2) hcol
        (extendLetters σ e.1) (extendLetters σ e.2)
      exact lt_of_lt_of_le hBoundPos hlower.1
  · apply Finset.prod_pos
    intro e he
    have hcol : κ e.1 ≠ κ e.2 := hκ e.1 e.2 (originalLegs_adjacent he)
    have hlower := hBounds (κ e.1) (κ e.2) hcol
      (extendLetters σ e.1) (extendBoundary η e.2)
    exact lt_of_lt_of_le hBoundPos hlower.1

end AKLT.W.WIN074
