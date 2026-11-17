module
public import AKLT.Blueprint.Win.NodesTopology

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

open AKLT.Defs

namespace AKLT.W.WIN019

theorem main : AKLT.Blueprint.Win.CutEdgesNonemptyStatement := by
  classical
  intro A hA
  obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image A (fun p : Plane => p.1) hA
  let y : Plane := (x.1 + 1, x.2)
  have hyA : y ∉ A := by
    intro hy
    have hcoord := hmax y hy
    dsimp [y] at hcoord
    omega
  have hstar : y ∈ AKLT.Blueprint.Win.starBall x := by
    dsimp [y, AKLT.Blueprint.Win.starBall]
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_Icc.mpr
      omega
    · apply Finset.mem_Icc.mpr
      omega
  have hedge : s(x, y) ∈ AKLT.Blueprint.Win.cutEdges A := by
    unfold AKLT.Blueprint.Win.cutEdges
    apply Finset.mem_biUnion.mpr
    refine ⟨x, hx, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨y, Finset.mem_sdiff.mpr ⟨hstar, hyA⟩, rfl⟩
  exact ⟨s(x, y), hedge⟩

end AKLT.W.WIN019

#print axioms AKLT.W.WIN019.main
