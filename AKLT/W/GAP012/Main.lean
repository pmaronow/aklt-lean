module
public import AKLT.Blueprint.Gap.NodesFinite

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Gap

namespace AKLT.W.GAP012

private theorem internalBonds_adjacent {W : Finset Plane} {e : Plane × Plane}
    (he : e ∈ internalBonds W) : Adjacent e.1 e.2 := by
  unfold internalBonds at he
  rcases Finset.mem_biUnion.mp he with ⟨x, hx, hxe⟩
  rcases Finset.mem_image.mp hxe with ⟨y, hy, hxy⟩
  have hypos : y ∈ positiveNeighbors x := (Finset.mem_inter.mp hy).1
  have heq : e = (x, y) := hxy.symm
  subst e
  simp only [positiveNeighbors, Finset.mem_insert, Finset.mem_singleton] at hypos
  rcases hypos with hypos | hypos
  · cases hypos
    simp [Adjacent, latticeDist]
  · cases hypos
    simp [Adjacent, latticeDist]

theorem main : FrameInteractionBoundsStatement := by
  intro hBounds hPositive hLess κ hColor W σ
  constructor
  · let B := internalBonds W
    have hLower : (frameBound : ℝ) ^ B.card ≤
        ∏ e ∈ B, (1 + dot (frameVector (κ e.1) (extendLetters σ e.1))
          (frameVector (κ e.2) (extendLetters σ e.2))) := by
      calc
        (frameBound : ℝ) ^ B.card = ∏ _e ∈ B, frameBound := by simp
        _ ≤ ∏ e ∈ B, (1 + dot (frameVector (κ e.1) (extendLetters σ e.1))
            (frameVector (κ e.2) (extendLetters σ e.2))) := by
          apply Finset.prod_le_prod₀
          · intro e he
            exact le_of_lt hPositive
          · intro e he
            have hAdj := internalBonds_adjacent he
            have hDistinct := hColor e.1 e.2 hAdj
            exact (hBounds (κ e.1) (κ e.2) hDistinct
              (extendLetters σ e.1) (extendLetters σ e.2)).1
    simpa [planeInteraction, B] using hLower
  · let B := internalBonds W
    have hUpper :
        ∏ e ∈ B, (1 + dot (frameVector (κ e.1) (extendLetters σ e.1))
          (frameVector (κ e.2) (extendLetters σ e.2))) ≤ (2-frameBound) ^ B.card := by
      calc
        ∏ e ∈ B, (1 + dot (frameVector (κ e.1) (extendLetters σ e.1))
            (frameVector (κ e.2) (extendLetters σ e.2)))
          ≤ ∏ e ∈ B, (2-frameBound) := by
            apply Finset.prod_le_prod₀
            · intro e he
              have hAdj := internalBonds_adjacent he
              have hDistinct := hColor e.1 e.2 hAdj
              have hFactor := hBounds (κ e.1) (κ e.2) hDistinct
                (extendLetters σ e.1) (extendLetters σ e.2)
              linarith [hPositive, hFactor.1]
            · intro e he
              have hAdj := internalBonds_adjacent he
              have hDistinct := hColor e.1 e.2 hAdj
              exact (hBounds (κ e.1) (κ e.2) hDistinct
                (extendLetters σ e.1) (extendLetters σ e.2)).2
        _ = (2-frameBound) ^ B.card := by simp
    simpa [planeInteraction, B] using hUpper

end AKLT.W.GAP012

#print axioms AKLT.W.GAP012.main
