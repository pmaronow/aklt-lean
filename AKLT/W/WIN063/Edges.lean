module
public import AKLT.Blueprint.Win.NodesCut

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Win

namespace AKLT.W.WIN063

lemma mem_pos (x y : Plane) : y ∈ positiveNeighbours x ↔ y = (x.1 + 1, x.2) ∨ y = (x.1, x.2 + 1) := by
  simp [positiveNeighbours]

lemma mem_orig (G : Finset Plane) (x y : Plane) :
    (x, y) ∈ originalLegs G ↔ x ∈ G ∧ y ∉ G ∧ y ∈ neighbours x := by
  simp [originalLegs, Finset.mem_biUnion, Finset.mem_image, Finset.mem_sdiff]
  tauto

lemma mem_bonds (G : Finset Plane) (x y : Plane) :
    (x, y) ∈ internalBonds G ↔ x ∈ G ∧ y ∈ G ∧ y ∈ positiveNeighbours x := by
  simp [internalBonds, Finset.mem_biUnion, Finset.mem_image]
  tauto


lemma add_east (x : Plane) : x + (1, 0) = (x.1 + 1, x.2) := by
  apply Prod.ext <;> simp [Prod.fst_add, Prod.snd_add]
lemma add_north (x : Plane) : x + (0, 1) = (x.1, x.2 + 1) := by
  apply Prod.ext <;> simp [Prod.fst_add, Prod.snd_add]
lemma add_west (x : Plane) : x + (-1, 0) = (x.1 + -1, x.2) := by
  apply Prod.ext <;> simp [Prod.fst_add, Prod.snd_add]
lemma add_south (x : Plane) : x + (0, -1) = (x.1, x.2 + -1) := by
  apply Prod.ext <;> simp [Prod.fst_add, Prod.snd_add]

lemma neigh_pos_cover {x y : Plane} (h : y ∈ neighbours x) :
    y ∈ positiveNeighbours x ∨ x ∈ positiveNeighbours y := by
  rcases Finset.mem_image.mp h with ⟨d, hd, rfl⟩
  cases d
  · left
    simp [positiveNeighbours, Compass.step, add_east]
  · left
    simp [positiveNeighbours, Compass.step, add_north]
  · right
    simp [positiveNeighbours, Compass.step, add_west]
  · right
    simp [positiveNeighbours, Compass.step, add_south]



lemma adjacent_of_mem_neighbours {x y : Plane} (h : y ∈ neighbours x) : Adjacent x y := by
  rcases Finset.mem_image.mp h with ⟨d, hd, rfl⟩
  cases d <;>
    simp [Adjacent, latticeDist, Compass.step, add_east, add_north, add_west, add_south,
      Int.natAbs] <;> rfl


lemma pos_asymm {x y : Plane} (h : y ∈ positiveNeighbours x) :
    x ∉ positiveNeighbours y := by
  intro hxy
  cases x with
  | mk a b =>
    cases y with
    | mk c d =>
      simp only [positiveNeighbours, Finset.mem_insert, Finset.mem_singleton,
        Prod.mk.injEq] at h hxy
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases hxy with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega

lemma pos_mem_neigh {x y : Plane} (h : y ∈ positiveNeighbours x) :
    y ∈ neighbours x ∧ x ∈ neighbours y := by
  rcases (mem_pos _ _).mp h with h | h
  · rw [h]
    constructor
    · apply Finset.mem_image.mpr
      refine ⟨Compass.east, by simp, ?_⟩
      simp [Compass.step, add_east]
    · apply Finset.mem_image.mpr
      refine ⟨Compass.west, by simp, ?_⟩
      simp [Compass.step]
  · rw [h]
    constructor
    · apply Finset.mem_image.mpr
      refine ⟨Compass.north, by simp, ?_⟩
      simp [Compass.step, add_north]
    · apply Finset.mem_image.mpr
      refine ⟨Compass.south, by simp, ?_⟩
      simp [Compass.step]


private def orient (e : Plane × Plane) : Plane × Plane :=
  if e.2 ∈ positiveNeighbours e.1 then e else e.swap

private lemma orient_eq_imp {e f : Plane × Plane} (h : orient e = orient f) :
    e = f ∨ e = f.swap := by
  by_cases he : e.2 ∈ positiveNeighbours e.1 <;>
    by_cases hf : f.2 ∈ positiveNeighbours f.1
  · exact Or.inl (by simpa [orient, he, hf] using h)
  · exact Or.inr (by simpa [orient, he, hf] using h)
  · right
    have hh : e.swap = f := by simpa [orient, he, hf] using h
    simpa using congrArg Prod.swap hh
  · left
    have hh : e.swap = f.swap := by simpa [orient, he, hf] using h
    simpa using congrArg Prod.swap hh

private lemma orient_inj (G : Finset Plane) :
    Set.InjOn orient (↑(originalLegs G) : Set (Plane × Plane)) := by
  intro e he f hf h
  rcases orient_eq_imp h with h | h
  · exact h
  · have he' := (mem_orig G e.1 e.2).mp he
    have hf' := (mem_orig G f.1 f.2).mp hf
    exact (hf'.2.1 (by simpa [h] using he'.1)).elim

private lemma mem_oriented_legs (G : Finset Plane) (e : Plane × Plane) :
    e ∈ (originalLegs G).image orient ↔
      e.2 ∈ positiveNeighbours e.1 ∧
        ((e.1 ∈ G ∧ e.2 ∉ G) ∨ (e.2 ∈ G ∧ e.1 ∉ G)) := by
  constructor
  · intro h
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hf1, hf2, hfn⟩ := (mem_orig G f.1 f.2).mp hf
    by_cases hp : f.2 ∈ positiveNeighbours f.1
    · simp [orient, hp, hf1, hf2]
    · have hr := (neigh_pos_cover hfn).resolve_left hp
      simp [orient, hp, hr, hf1, hf2]
  · rintro ⟨hp, (⟨h1, h2⟩ | ⟨h2, h1⟩)⟩
    · refine Finset.mem_image.mpr ⟨e, ?_, ?_⟩
      · exact (mem_orig G _ _).mpr ⟨h1, h2, (pos_mem_neigh hp).1⟩
      · simp [orient, hp]
    · refine Finset.mem_image.mpr ⟨e.swap, ?_, ?_⟩
      · exact (mem_orig G _ _).mpr ⟨h2, h1, (pos_mem_neigh hp).2⟩
      · simp [orient, pos_asymm hp]

/-- Each physical edge meeting the volume, counted in positive orientation. -/
private def volumeEdges (G : Finset Plane) : Finset (Plane × Plane) :=
  internalBonds G ∪ (originalLegs G).image orient

private lemma mem_volumeEdges (G : Finset Plane) (e : Plane × Plane) :
    e ∈ volumeEdges G ↔
      e.2 ∈ positiveNeighbours e.1 ∧ (e.1 ∈ G ∨ e.2 ∈ G) := by
  rcases e with ⟨x, y⟩
  simp only [volumeEdges, Finset.mem_union, mem_bonds, mem_oriented_legs]
  tauto

private lemma disjoint_edges (G : Finset Plane) :
    Disjoint (internalBonds G) ((originalLegs G).image orient) := by
  apply Finset.disjoint_left.mpr
  intro e hi hl
  obtain ⟨h1, h2, _⟩ := (mem_bonds G e.1 e.2).mp hi
  obtain ⟨_, h | h⟩ := (mem_oriented_legs G e).mp hl
  · exact h.2 h2
  · exact h.2 h1

private lemma prod_volumeEdges (G : Finset Plane) (f : Plane × Plane → ℝ)
    (hsymm : ∀ e, f e.swap = f e) :
    (∏ e ∈ volumeEdges G, f e) =
      (∏ e ∈ internalBonds G, f e) * ∏ e ∈ originalLegs G, f e := by
  classical
  rw [volumeEdges, Finset.prod_union (disjoint_edges G),
    Finset.prod_image (orient_inj G)]
  congr 1
  apply Finset.prod_congr rfl
  intro e he
  dsimp [orient]
  split_ifs
  · rfl
  · exact hsymm e

private lemma volumeEdges_split {F B : Finset Plane} (hBF : B ⊆ F)
    (hNo : NoBond (↑B) {z | z ∉ F}) :
    volumeEdges F = internalBonds B ∪ volumeEdges (F \ B) := by
  classical
  ext ⟨x, y⟩
  simp only [Finset.mem_union, mem_volumeEdges, mem_bonds, Finset.mem_sdiff]
  constructor
  · rintro ⟨hp, hxF | hyF⟩
    · by_cases hxB : x ∈ B
      · by_cases hyB : y ∈ B
        · exact Or.inl ⟨hxB, hyB, hp⟩
        · have hyF : y ∈ F := by
            by_contra hyF
            exact hNo x hxB y hyF (adjacent_of_mem_neighbours (pos_mem_neigh hp).1)
          exact Or.inr ⟨hp, Or.inr ⟨hyF, hyB⟩⟩
      · exact Or.inr ⟨hp, Or.inl ⟨hxF, hxB⟩⟩
    · by_cases hyB : y ∈ B
      · by_cases hxB : x ∈ B
        · exact Or.inl ⟨hxB, hyB, hp⟩
        · have hxF : x ∈ F := by
            by_contra hxF
            exact hNo y hyB x hxF (adjacent_of_mem_neighbours (pos_mem_neigh hp).2)
          exact Or.inr ⟨hp, Or.inl ⟨hxF, hxB⟩⟩
      · exact Or.inr ⟨hp, Or.inr ⟨hyF, hyB⟩⟩
  · rintro (⟨hxB, hyB, hp⟩ | ⟨hp, ⟨hxF, _⟩ | ⟨hyF, _⟩⟩)
    · exact ⟨hp, Or.inl (hBF hxB)⟩
    · exact ⟨hp, Or.inl hxF⟩
    · exact ⟨hp, Or.inr hyF⟩

/-- Splitting a symmetric edge product at an interior window retains exactly
the original legs of its complement. -/
theorem split_edge_products {F B : Finset Plane} (hBF : B ⊆ F)
    (hNo : NoBond (↑B) {z | z ∉ F})
    (f : Plane × Plane → ℝ) (hsymm : ∀ e, f e.swap = f e) :
    (∏ e ∈ internalBonds F, f e) * (∏ e ∈ originalLegs F, f e) =
      (∏ e ∈ internalBonds B, f e) *
        ((∏ e ∈ internalBonds (F \ B), f e) * ∏ e ∈ originalLegs (F \ B), f e) := by
  classical
  have hd : Disjoint (internalBonds B) (volumeEdges (F \ B)) := by
    apply Finset.disjoint_left.mpr
    intro e heB heG
    obtain ⟨hxB, hyB, _⟩ := (mem_bonds B e.1 e.2).mp heB
    obtain ⟨_, h | h⟩ := (mem_volumeEdges (F \ B) e).mp heG
    · exact (Finset.mem_sdiff.mp h).2 hxB
    · exact (Finset.mem_sdiff.mp h).2 hyB
  rw [← prod_volumeEdges F f hsymm, volumeEdges_split hBF hNo,
    Finset.prod_union hd, prod_volumeEdges (F \ B) f hsymm]

end AKLT.W.WIN063
