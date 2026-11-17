module
public import AKLT.Blueprint.Win.NodesTopology

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section

open AKLT.Defs

namespace AKLT.W.WIN018

theorem main : AKLT.Blueprint.Win.PlaquetteTrianglesStatement := by
  intro p
  have h₁ :
      AKLT.Blueprint.Win.triangle p (p + (1, 0)) (p + (1, 1)) ∈
        AKLT.Blueprint.Win.triangleSpan := by
    apply Submodule.subset_span
    refine ⟨p, p + (1, 0), p + (1, 1), ?_, rfl⟩
    unfold AKLT.Blueprint.Win.IsTriangle AKLT.Blueprint.Win.StarAdjacent
      AKLT.Defs.supDist
    simp [AKLT.Defs.Plane]
  have h₂ :
      AKLT.Blueprint.Win.triangle p (p + (1, 1)) (p + (0, 1)) ∈
        AKLT.Blueprint.Win.triangleSpan := by
    apply Submodule.subset_span
    refine ⟨p, p + (1, 1), p + (0, 1), ?_, rfl⟩
    unfold AKLT.Blueprint.Win.IsTriangle AKLT.Blueprint.Win.StarAdjacent
      AKLT.Defs.supDist
    simp [AKLT.Defs.Plane]
  have hsum := Submodule.add_mem AKLT.Blueprint.Win.triangleSpan h₁ h₂
  have hdecomp : AKLT.Blueprint.Win.plaquette p =
      AKLT.Blueprint.Win.triangle p (p + (1, 0)) (p + (1, 1)) +
      AKLT.Blueprint.Win.triangle p (p + (1, 1)) (p + (0, 1)) := by
    ext e
    simp only [AKLT.Blueprint.Win.plaquette, AKLT.Blueprint.Win.triangle,
      AKLT.Blueprint.Win.edge, Finsupp.add_apply, Finsupp.single_apply,
      Sym2.eq_swap]
    ring_nf
    norm_num
    intro _
    exact ZMod.natCast_self 2
  rw [hdecomp]
  exact hsum

end AKLT.W.WIN018

#print axioms AKLT.W.WIN018.main
