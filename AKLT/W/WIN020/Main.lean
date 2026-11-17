import AKLT.Blueprint.Win.NodesTopology

noncomputable section

namespace AKLT.W.WIN020

open AKLT.Blueprint.Win

/-- The finite linked component of a crossing edge separates any other
crossing edge that is not reachable from it. -/
theorem main : AKLT.Blueprint.Win.LinkedSeparationStatement := by
  classical
  intro A hnot
  let S : Set LatticeEdge := (cutEdges A : Set LatticeEdge)
  have hS : ∀ {e : LatticeEdge}, e ∈ cutEdges A ↔ e ∈ S := Iff.rfl
  push Not at hnot
  obtain ⟨e, he, f, hf, hnf⟩ := hnot
  let E : Finset LatticeEdge := (cutEdges A).filter (fun g => JoinedIn Linked S e g)
  refine ⟨E, ?_⟩
  constructor
  · constructor
    · intro g hg
      exact (Finset.mem_filter.mp hg).1
    · intro g hg g' hg' hgg'
      have hgcut : g ∈ cutEdges A := (Finset.mem_filter.mp hg).1
      have hgreach : JoinedIn Linked S e g := (Finset.mem_filter.mp hg).2
      have hg'path : JoinedIn Linked S e g' := by
        change Relation.ReflTransGen
          (fun v w => v ∈ S ∧ w ∈ S ∧ Linked v w) e g at hgreach
        apply hgreach.trans
        exact Relation.ReflTransGen.single
          ⟨(hS).2 hgcut, (hS).2 hg', hgg'⟩
      exact Finset.mem_filter.mpr ⟨hg', hg'path⟩
  · refine ⟨e, ?_, f, hf, ?_⟩
    · exact Finset.mem_filter.mpr ⟨he, by
        change Relation.ReflTransGen
          (fun v w => v ∈ S ∧ w ∈ S ∧ Linked v w) e e
        exact Relation.ReflTransGen.refl⟩
    · intro hfE
      exact hnf (Finset.mem_filter.mp hfE |>.2)

#print axioms main

end AKLT.W.WIN020
