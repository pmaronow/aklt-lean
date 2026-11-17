module
public import AKLT.Blueprint.Q.NodesEnergy

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Challenge

namespace AKLT.W.Q049

private theorem frameBound_pos : 0 < frameBound := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hn := Real.sqrt_nonneg (5 : ℝ)
  have hlt : Real.sqrt 5 < 5 := by nlinarith
  unfold frameBound
  exact div_pos (by linarith) (by norm_num)

private theorem plus_factor_pos (hB : AKLT.Blueprint.Q.interactionBounds)
    {i j : Fin 3} (hij : i ≠ j) (a b : IcoLetter) :
    0 < 1 + dot (frameVector i a) (frameVector j b) :=
  lt_of_lt_of_le frameBound_pos (hB i j hij a b).1

private theorem minus_factor_pos (hB : AKLT.Blueprint.Q.interactionBounds)
    {i j : Fin 3} (hij : i ≠ j) (a b : IcoLetter) :
    0 < 1 - dot (frameVector i a) (frameVector j b) :=
  lt_of_lt_of_le frameBound_pos (hB i j hij a b).2.2.1

private theorem adjacent_of_positiveNeighbours {x y : Plane}
    (hy : y ∈ positiveNeighbours x) : Adjacent x y := by
  simp only [positiveNeighbours, Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with hy | hy
  · subst y
    simp [Adjacent, latticeDist]
  · subst y
    simp [Adjacent, latticeDist]

private theorem adjacent_of_neighbours {x y : Plane}
    (hy : y ∈ neighbours x) : Adjacent x y := by
  unfold neighbours at hy
  rcases Finset.mem_image.mp hy with ⟨d, _, rfl⟩
  cases d <;> simp [Adjacent, latticeDist, Compass.step]

private theorem originalLeg_adjacent {W : Finset Plane} {e : Plane × Plane}
    (he : e ∈ originalLegs W) : Adjacent e.1 e.2 := by
  unfold originalLegs at he
  rcases Finset.mem_biUnion.mp he with ⟨x, hx, he⟩
  rcases Finset.mem_image.mp he with ⟨z, hz, heq⟩
  have hneigh : z ∈ neighbours x := (Finset.mem_sdiff.mp hz).1
  have heq' : e = (x, z) := heq.symm
  have hxy : Adjacent x z := adjacent_of_neighbours hneigh
  have hfst : e.1 = x := congrArg Prod.fst heq'
  have hsnd : e.2 = z := congrArg Prod.snd heq'
  simpa [hfst, hsnd] using hxy

private theorem originalLeg_first_mem {W : Finset Plane} {e : Plane × Plane}
    (he : e ∈ originalLegs W) : e.1 ∈ W := by
  unfold originalLegs at he
  rcases Finset.mem_biUnion.mp he with ⟨x, hx, he⟩
  rcases Finset.mem_image.mp he with ⟨z, hz, heq⟩
  have heq' : e = (x, z) := heq.symm
  simpa [heq'] using hx

theorem main : AKLT.Blueprint.Q.FrameWeightsPositiveStatement := by
  intro hB
  constructor
  · intro κ hκ W η σ
    unfold planeWeight
    refine mul_pos ?_ ?_
    · refine mul_pos ?_ ?_
      · exact pow_pos (by norm_num : (0 : ℝ) < 1 / 12) W.card
      · refine Finset.prod_pos ?_
        intro e he
        unfold internalBonds at he
        rcases Finset.mem_biUnion.mp he with ⟨x, hx, he⟩
        rcases Finset.mem_image.mp he with ⟨y, hy, heq⟩
        have hypos : y ∈ positiveNeighbours x := (Finset.mem_inter.mp hy).1
        have hyW : y ∈ W := (Finset.mem_inter.mp hy).2
        have hpair : e = (x, y) := heq.symm
        have hxy : Adjacent x y := adjacent_of_positiveNeighbours hypos
        have hcol : κ x ≠ κ y := hκ x y hxy
        have hpos := plus_factor_pos hB hcol
          (extendLetters σ x) (extendLetters σ y)
        have hfst : e.1 = x := congrArg Prod.fst hpair
        have hsnd : e.2 = y := congrArg Prod.snd hpair
        simpa [hfst, hsnd, extendLetters, hx, hyW] using hpos
    · refine Finset.prod_pos ?_
      intro e he
      have hxW : e.1 ∈ W := originalLeg_first_mem he
      have hxy : Adjacent e.1 e.2 := originalLeg_adjacent he
      have hcol : κ e.1 ≠ κ e.2 := hκ e.1 e.2 hxy
      simpa [extendLetters, hxW] using
        plus_factor_pos hB hcol (σ ⟨e.1, hxW⟩) (extendBoundary η e.2)
  · intro L N κ hκ σ
    unfold torusWeight
    apply mul_pos
    · apply Finset.prod_pos
      intro x hx
      norm_num
    · apply Finset.prod_pos
      intro e he
      exact minus_factor_pos hB (hκ e)
        (σ e.1) (σ (nextSite e.1 e.2))

end AKLT.W.Q049
