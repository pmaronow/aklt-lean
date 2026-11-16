import AKLT.Blueprint.Win.NodesTopology

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Win

namespace AKLT.W.WIN021

private theorem starBall_mem_of_starAdjacent {x y : Plane}
    (h : StarAdjacent x y) : y ∈ starBall x := by
  unfold StarAdjacent supDist at h
  unfold starBall
  change y ∈ (Finset.Icc (x.1 - 1) (x.1 + 1) ×ˢ
    Finset.Icc (x.2 - 1) (x.2 + 1))
  simp only [Finset.mem_product, Finset.mem_Icc]
  constructor
  · constructor
    · have h1 : (x.1 - y.1).natAbs ≤ 1 := by
        calc
          (x.1 - y.1).natAbs ≤ max (x.1 - y.1).natAbs (x.2 - y.2).natAbs := Nat.le_max_left _ _
          _ = 1 := h
      omega
    · have h1 : (x.1 - y.1).natAbs ≤ 1 := by
        calc
          (x.1 - y.1).natAbs ≤ max (x.1 - y.1).natAbs (x.2 - y.2).natAbs := Nat.le_max_left _ _
          _ = 1 := h
      omega
  · constructor
    · have h1 : (x.2 - y.2).natAbs ≤ 1 := by
        calc
          (x.2 - y.2).natAbs ≤ max (x.1 - y.1).natAbs (x.2 - y.2).natAbs := Nat.le_max_right _ _
          _ = 1 := h
      omega
    · have h1 : (x.2 - y.2).natAbs ≤ 1 := by
        calc
          (x.2 - y.2).natAbs ≤ max (x.1 - y.1).natAbs (x.2 - y.2).natAbs := Nat.le_max_right _ _
          _ = 1 := h
      omega

private theorem cutEdges_mem_iff {A : Finset Plane} {x y : Plane}
    (hxy : StarAdjacent x y) :
    s(x, y) ∈ cutEdges A ↔
      (x ∈ A ∧ y ∉ A) ∨ (y ∈ A ∧ x ∉ A) := by
  constructor
  · intro he
    unfold cutEdges at he
    rcases Finset.mem_biUnion.mp he with ⟨u, hu, hmem⟩
    rcases Finset.mem_image.mp hmem with ⟨v, hv, heq⟩
    have hvout : v ∉ A := (Finset.mem_sdiff.mp hv).2
    rcases Sym2.eq_iff.mp heq with ⟨huX, hvY⟩ | ⟨huY, hvX⟩
    · exact Or.inl ⟨huX.symm ▸ hu, hvY.symm ▸ hvout⟩
    · exact Or.inr ⟨huY.symm ▸ hu, hvX.symm ▸ hvout⟩
  · intro hside
    unfold cutEdges
    rcases hside with ⟨hx, hy⟩ | ⟨hy, hx⟩
    · apply Finset.mem_biUnion.mpr
      refine ⟨x, hx, ?_⟩
      apply Finset.mem_image.mpr
      refine ⟨y, Finset.mem_sdiff.mpr ⟨starBall_mem_of_starAdjacent hxy, hy⟩, ?_⟩
      rfl
    · have hyx : StarAdjacent y x := metricFacts.2.2.2 x y hxy
      apply Finset.mem_biUnion.mpr
      refine ⟨y, hy, ?_⟩
      apply Finset.mem_image.mpr
      refine ⟨x, Finset.mem_sdiff.mpr ⟨starBall_mem_of_starAdjacent hyx, hx⟩, ?_⟩
      exact Sym2.eq_swap

private theorem cutParity_add (E : Finset LatticeEdge) (c d : EdgeChain) :
    cutParity E (c + d) = cutParity E c + cutParity E d := by
  simp [cutParity, Finset.sum_add_distrib]

private theorem cutParity_edge (E : Finset LatticeEdge) (x y : Plane) :
    cutParity E (edge x y) = if s(x, y) ∈ E then 1 else 0 := by
  simp only [cutParity, edge, Finsupp.single_apply, Finset.sum_ite_eq]

private theorem cutParity_triangle_formula (E : Finset LatticeEdge)
    (x y z : Plane) :
    cutParity E (triangle x y z) =
      (if s(x, y) ∈ E then 1 else 0) +
      (if s(y, z) ∈ E then 1 else 0) +
      (if s(z, x) ∈ E then 1 else 0) := by
  unfold triangle
  rw [cutParity_add, cutParity_add]
  rw [cutParity_edge, cutParity_edge, cutParity_edge]

private theorem linked_symm {e f : LatticeEdge} (h : Linked e f) : Linked f e := by
  rcases h with ⟨x, y, z, ht, he, hf⟩
  exact ⟨x, y, z, ht, hf, he⟩

private theorem mem_E_iff_of_linked {A : Finset Plane} {E : Finset LatticeEdge}
    (hE : LinkClosed A E) {e f : LatticeEdge}
    (he : e ∈ cutEdges A) (hf : f ∈ cutEdges A) (hl : Linked e f) :
    e ∈ E ↔ f ∈ E := by
  constructor
  · intro h
    exact hE.2 e h f hf hl
  · intro h
    exact hE.2 f h e he (linked_symm hl)

private theorem not_mem_E_of_sameSide {A : Finset Plane} {E : Finset LatticeEdge}
    (hE : LinkClosed A E) {x y : Plane} (hxy : StarAdjacent x y)
    (hsame : (x ∈ A) ↔ (y ∈ A)) : s(x, y) ∉ E := by
  intro he
  have hc : s(x, y) ∈ cutEdges A := hE.1 he
  rcases (cutEdges_mem_iff hxy).mp hc with ⟨hx, hy⟩ | ⟨hy, hx⟩
  · exact hy (hsame.mp hx)
  · exact hx (hsame.mpr hy)

private theorem indicator_pair_cancel {p q : Prop} [Decidable p] [Decidable q]
    (h : p ↔ q) :
    (if p then (1 : ZMod 2) else 0) + (if q then 1 else 0) = 0 := by
  by_cases hp : p
  · have hq : q := h.mp hp
    simp [hp, hq]
    decide
  · have hq : ¬ q := fun hq => hp (h.mpr hq)
    simp [hp, hq]

theorem main : AKLT.Blueprint.Win.TriangleCutParityStatement := by
  intro A E hE x y z htri
  rcases htri with ⟨hxy, hyz, hzx⟩
  have hsame : (x ∈ A ↔ y ∈ A) ∨ (y ∈ A ↔ z ∈ A) ∨ (z ∈ A ↔ x ∈ A) := by
    tauto
  have hlink12 : Linked s(x, y) s(y, z) := by
    exact ⟨x, y, z, ⟨hxy, hyz, hzx⟩, by simp, by simp⟩
  have hlink23 : Linked s(y, z) s(z, x) := by
    exact ⟨x, y, z, ⟨hxy, hyz, hzx⟩, by simp, by simp⟩
  have hlink31 : Linked s(z, x) s(x, y) := by
    exact ⟨x, y, z, ⟨hxy, hyz, hzx⟩, by simp, by simp⟩
  rw [cutParity_triangle_formula]
  by_cases hxyS : (x ∈ A) ↔ (y ∈ A)
  · by_cases hyzS : (y ∈ A) ↔ (z ∈ A)
    · have hzxS : (z ∈ A) ↔ (x ∈ A) := (hxyS.trans hyzS).symm
      have hn1 := not_mem_E_of_sameSide hE hxy hxyS
      have hn2 := not_mem_E_of_sameSide hE hyz hyzS
      have hn3 := not_mem_E_of_sameSide hE hzx hzxS
      simp [hn1, hn2, hn3]
    · have hn1 := not_mem_E_of_sameSide hE hxy hxyS
      have hc2 : s(y, z) ∈ cutEdges A := by
        apply (cutEdges_mem_iff hyz).2
        tauto
      have hc3 : s(z, x) ∈ cutEdges A := by
        apply (cutEdges_mem_iff hzx).2
        tauto
      have hpair := mem_E_iff_of_linked hE hc2 hc3 hlink23
      simpa [hn1] using indicator_pair_cancel hpair
  · by_cases hyzS : (y ∈ A) ↔ (z ∈ A)
    · have hn2 := not_mem_E_of_sameSide hE hyz hyzS
      have hc1 : s(x, y) ∈ cutEdges A := by
        apply (cutEdges_mem_iff hxy).2
        tauto
      have hc3 : s(z, x) ∈ cutEdges A := by
        apply (cutEdges_mem_iff hzx).2
        tauto
      have hpair := (mem_E_iff_of_linked hE hc3 hc1 hlink31).symm
      simpa [hn2] using indicator_pair_cancel hpair
    · have hzxS : (z ∈ A) ↔ (x ∈ A) := by
        rcases hsame with h | h
        · exact False.elim (hxyS h)
        · rcases h with h | h
          · exact False.elim (hyzS h)
          · exact h
      have hn3 := not_mem_E_of_sameSide hE hzx hzxS
      have hc1 : s(x, y) ∈ cutEdges A := by
        apply (cutEdges_mem_iff hxy).2
        tauto
      have hc2 : s(y, z) ∈ cutEdges A := by
        apply (cutEdges_mem_iff hyz).2
        tauto
      have hpair := mem_E_iff_of_linked hE hc1 hc2 hlink12
      simpa [hn3] using indicator_pair_cancel hpair

#print axioms main

end AKLT.W.WIN021
