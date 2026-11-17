module
public import AKLT.Blueprint.Win.NodesTopology

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open AKLT.Defs

namespace AKLT.W.WIN024

open AKLT.Blueprint.Win

private lemma cutEdge_rep {A : Finset Plane} {e : LatticeEdge}
    (he : e ∈ cutEdges A) :
    ∃ x y, x ∈ A ∧ y ∉ A ∧ y ∈ starBall x ∧ e = s(x, y) := by
  classical
  unfold cutEdges at he
  rw [Finset.mem_biUnion] at he
  obtain ⟨x, hx, he⟩ := he
  rw [Finset.mem_image] at he
  obtain ⟨y, hy, rfl⟩ := he
  rw [Finset.mem_sdiff] at hy
  exact ⟨x, y, hx, hy.2, hy.1, rfl⟩

private lemma cutEdge_has_outside {A : Finset Plane} {e : LatticeEdge}
    (he : e ∈ cutEdges A) : ∃ z, z ∉ A ∧ z ∈ e := by
  obtain ⟨x, y, hx, hy, hball, hedge⟩ := cutEdge_rep he
  exact ⟨y, hy, by simp [hedge]⟩

private noncomputable def outsideData (A : Finset Plane) (e : LatticeEdge)
    (he : e ∈ cutEdges A) : {z : Plane // z ∉ A ∧ z ∈ e} := by
  classical
  let p := cutEdge_has_outside he
  exact ⟨Classical.choose p, Classical.choose_spec p⟩

private noncomputable def outsideEndpoint (A : Finset Plane) (e : LatticeEdge) : Plane :=
  if he : e ∈ cutEdges A then (outsideData A e he).val else (0, 0)

private lemma outsideEndpoint_spec {A : Finset Plane} {e : LatticeEdge}
    (he : e ∈ cutEdges A) : outsideEndpoint A e ∉ A ∧ outsideEndpoint A e ∈ e := by
  unfold outsideEndpoint
  rw [dite_eq_left he]
  exact (outsideData A e he).property

private lemma cutEdge_outside_unique {A : Finset Plane} {e : LatticeEdge}
    (he : e ∈ cutEdges A) {z w : Plane}
    (hzA : z ∉ A) (hze : z ∈ e) (hwA : w ∉ A) (hwe : w ∈ e) : z = w := by
  obtain ⟨x, y, hx, hy, hball, hedge⟩ := cutEdge_rep he
  have hz : z = x ∨ z = y := by simpa [hedge] using hze
  have hw : w = x ∨ w = y := by simpa [hedge] using hwe
  rcases hz with rfl | rfl
  · exact (hzA hx).elim
  · rcases hw with h | h
    · exact (hwA (h ▸ hx)).elim
    · exact h.symm

private lemma outside_endpoint_unique {A : Finset Plane} {e : LatticeEdge}
    (he : e ∈ cutEdges A) {z : Plane} (hzA : z ∉ A) (hze : z ∈ e) :
    z = outsideEndpoint A e :=
  cutEdge_outside_unique he hzA hze (outsideEndpoint_spec he).1 (outsideEndpoint_spec he).2

private lemma outsideEndpoint_mem_rawBoundary {A : Finset Plane} {e : LatticeEdge}
    (he : e ∈ cutEdges A) : outsideEndpoint A e ∈ rawBoundary A := by
  obtain ⟨x, y, hx, hy, hball, hedge⟩ := cutEdge_rep he
  have hout : outsideEndpoint A e = y := by
    symm
    exact outside_endpoint_unique he hy (by simp [hedge])
  rw [hout, rawBoundary, Finset.mem_sdiff, Finset.mem_biUnion]
  exact ⟨⟨x, hx, hball⟩, hy⟩

private lemma rawBoundary_has_edge {A : Finset Plane} {z : Plane}
    (hz : z ∈ rawBoundary A) :
    ∃ e : LatticeEdge, e ∈ cutEdges A ∧ outsideEndpoint A e = z := by
  unfold rawBoundary at hz
  rw [Finset.mem_sdiff] at hz
  rcases hz with ⟨hzUnion, hzA⟩
  rw [Finset.mem_biUnion] at hzUnion
  rcases hzUnion with ⟨x, hx, hball⟩
  have he : s(x, z) ∈ cutEdges A := by
    unfold cutEdges
    rw [Finset.mem_biUnion]
    refine ⟨x, hx, ?_⟩
    rw [Finset.mem_image]
    exact ⟨z, Finset.mem_sdiff.mpr ⟨hball, hzA⟩, rfl⟩
  refine ⟨s(x, z), he, ?_⟩
  symm
  exact outside_endpoint_unique he hzA (Sym2.mem_mk_right x z)

private lemma starAdjacent_symm {x y : Plane} (h : StarAdjacent x y) :
    StarAdjacent y x := by
  have hsub : ∀ a b : ℤ, (a - b).natAbs = (b - a).natAbs := by
    intro a b
    calc
      (a - b).natAbs = (-(a - b)).natAbs := (Int.natAbs_neg _).symm
      _ = (b - a).natAbs := by rw [neg_sub]
  simpa only [StarAdjacent, supDist, hsub x.1 y.1, hsub x.2 y.2] using h

private lemma linked_outside_related {A : Finset Plane} {e f : LatticeEdge}
    (he : e ∈ cutEdges A) (hf : f ∈ cutEdges A) (hl : Linked e f) :
    outsideEndpoint A e = outsideEndpoint A f ∨
      StarAdjacent (outsideEndpoint A e) (outsideEndpoint A f) := by
  obtain ⟨x, y, z, htri, hetri, hftri⟩ := hl
  have heverts : outsideEndpoint A e = x ∨
      outsideEndpoint A e = y ∨ outsideEndpoint A e = z := by
    have hmem : e ∈ ({s(x, y), s(y, z), s(z, x)} : Finset LatticeEdge) := hetri
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h
    · have hm : outsideEndpoint A e ∈ s(x, y) := by
        simpa [h] using (outsideEndpoint_spec he).2
      rcases (show outsideEndpoint A e = x ∨ outsideEndpoint A e = y by simpa using hm) with hx | hy
      · exact Or.inl hx
      · exact Or.inr (Or.inl hy)
    · have hm : outsideEndpoint A e ∈ s(y, z) := by
        simpa [h] using (outsideEndpoint_spec he).2
      rcases (show outsideEndpoint A e = y ∨ outsideEndpoint A e = z by simpa using hm) with hy | hz
      · exact Or.inr (Or.inl hy)
      · exact Or.inr (Or.inr hz)
    · have hm : outsideEndpoint A e ∈ s(z, x) := by
        simpa [h] using (outsideEndpoint_spec he).2
      rcases (show outsideEndpoint A e = z ∨ outsideEndpoint A e = x by simpa using hm) with hz | hx
      · exact Or.inr (Or.inr hz)
      · exact Or.inl hx
  have hfverts : outsideEndpoint A f = x ∨
      outsideEndpoint A f = y ∨ outsideEndpoint A f = z := by
    have hmem : f ∈ ({s(x, y), s(y, z), s(z, x)} : Finset LatticeEdge) := hftri
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h
    · have hm : outsideEndpoint A f ∈ s(x, y) := by
        simpa [h] using (outsideEndpoint_spec hf).2
      rcases (show outsideEndpoint A f = x ∨ outsideEndpoint A f = y by simpa using hm) with hx | hy
      · exact Or.inl hx
      · exact Or.inr (Or.inl hy)
    · have hm : outsideEndpoint A f ∈ s(y, z) := by
        simpa [h] using (outsideEndpoint_spec hf).2
      rcases (show outsideEndpoint A f = y ∨ outsideEndpoint A f = z by simpa using hm) with hy | hz
      · exact Or.inr (Or.inl hy)
      · exact Or.inr (Or.inr hz)
    · have hm : outsideEndpoint A f ∈ s(z, x) := by
        simpa [h] using (outsideEndpoint_spec hf).2
      rcases (show outsideEndpoint A f = z ∨ outsideEndpoint A f = x by simpa using hm) with hz | hx
      · exact Or.inr (Or.inr hz)
      · exact Or.inl hx
  rcases heverts with hx | hy | hz <;> rcases hfverts with hx' | hy' | hz'
  · exact Or.inl (hx.trans hx'.symm)
  · exact Or.inr (by simpa [hx, hy'] using htri.1)
  · exact Or.inr (by simpa [hx, hz'] using starAdjacent_symm htri.2.2)
  · exact Or.inr (by simpa [hy, hx'] using starAdjacent_symm htri.1)
  · exact Or.inl (hy.trans hy'.symm)
  · exact Or.inr (by simpa [hy, hz'] using htri.2.1)
  · exact Or.inr (by simpa [hz, hx'] using htri.2.2)
  · exact Or.inr (by simpa [hz, hy'] using starAdjacent_symm htri.2.1)
  · exact Or.inl (hz.trans hz'.symm)

private lemma linkedPath_outside_transfer {A : Finset Plane}
    {e f : LatticeEdge}
    (hp : JoinedIn Linked (↑(cutEdges A) : Set LatticeEdge) e f) :
    JoinedIn StarAdjacent (↑(rawBoundary A) : Set Plane)
      (outsideEndpoint A e) (outsideEndpoint A f) := by
  induction hp with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hab hbc ih =>
    rcases hbc with ⟨hb, hc, hlinked⟩
    have houter := linked_outside_related hb hc hlinked
    rcases houter with heq | hadj
    · simpa [heq] using ih
    · exact Relation.ReflTransGen.tail ih
        ⟨outsideEndpoint_mem_rawBoundary hb, outsideEndpoint_mem_rawBoundary hc, hadj⟩

theorem main : AKLT.Blueprint.Win.OuterEndpointTransferStatement := by
  intro A hcuts hlinked
  constructor
  · obtain ⟨e, he⟩ := hcuts
    exact ⟨outsideEndpoint A e, outsideEndpoint_mem_rawBoundary he⟩
  · intro z hz w hw
    obtain ⟨e, he, rfl⟩ := rawBoundary_has_edge hz
    obtain ⟨f, hf, rfl⟩ := rawBoundary_has_edge hw
    exact linkedPath_outside_transfer (hlinked e he f hf)

#print axioms main

end AKLT.W.WIN024
