module
public import AKLT.Defs.Response

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC003

theorem adjacent_symm {x z : Plane} (h : Adjacent x z) : Adjacent z x := by
  unfold Adjacent latticeDist at *
  rw [show z.1 - x.1 = -(x.1 - z.1) by ring,
    show z.2 - x.2 = -(x.2 - z.2) by ring]
  simpa only [Int.natAbs_neg] using h

theorem adjacent_ne {x z : Plane} (h : Adjacent x z) : x ≠ z := by
  intro heq
  subst z
  norm_num [Adjacent, latticeDist] at h

theorem adjacent_positive (x z : Plane) :
    Adjacent x z ↔ z ∈ positiveNeighbours x ∨ x ∈ positiveNeighbours z := by
  rcases x with ⟨x₁, x₂⟩
  rcases z with ⟨z₁, z₂⟩
  simp only [Adjacent, latticeDist, positiveNeighbours, Finset.mem_insert,
    Finset.mem_singleton, Prod.mk.injEq]
  omega

theorem positive_asymm {x z : Plane} (h : z ∈ positiveNeighbours x) :
    x ∉ positiveNeighbours z := by
  rcases x with ⟨x₁, x₂⟩
  rcases z with ⟨z₁, z₂⟩
  simp only [positiveNeighbours, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq] at *
  omega

theorem mem_neighbours (x z : Plane) : z ∈ neighbours x ↔ Adjacent x z := by
  rw [adjacent_positive]
  simp only [neighbours, Finset.mem_image]
  constructor
  · rintro ⟨d, _, rfl⟩
    cases d <;> simp [positiveNeighbours, Compass.step, Prod.ext_iff]
  · intro h
    rcases h with hp | hp
    · simp only [positiveNeighbours, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact ⟨.east, Finset.mem_univ _, by ext <;> simp [Compass.step]⟩
      · exact ⟨.north, Finset.mem_univ _, by ext <;> simp [Compass.step]⟩
    · simp only [positiveNeighbours, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with hp | hp
      · refine ⟨.west, Finset.mem_univ _, ?_⟩
        rw [hp]
        ext <;> simp [Compass.step]
      · refine ⟨.south, Finset.mem_univ _, ?_⟩
        rw [hp]
        ext <;> simp [Compass.step]

theorem mem_internal (G : Finset Plane) (e : Plane × Plane) :
    e ∈ internalBonds G ↔ e.1 ∈ G ∧ e.2 ∈ positiveNeighbours e.1 ∧ e.2 ∈ G := by
  constructor
  · intro he
    obtain ⟨x, hxG, he⟩ := Finset.mem_biUnion.mp he
    obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp he
    subst e
    exact ⟨hxG, (Finset.mem_inter.mp hz).1, (Finset.mem_inter.mp hz).2⟩
  · rintro ⟨hxG, hzN, hzG⟩
    exact Finset.mem_biUnion.mpr ⟨e.1, hxG,
      Finset.mem_image.mpr ⟨e.2, Finset.mem_inter.mpr ⟨hzN, hzG⟩, Prod.eta e⟩⟩

theorem present_symm {G : Finset Plane} {D : Network G} {x z : Plane}
    (h : D.Present x z) : D.Present z x :=
  ⟨h.2.1, h.1, adjacent_symm h.2.2.1, h.2.2.2.2, h.2.2.2.1⟩

theorem mem_presentNeighbours {G : Finset Plane} (D : Network G) (x z : Plane) :
    z ∈ D.presentNeighbours x ↔ D.Present x z := by
  simp only [Network.presentNeighbours, Finset.mem_filter]
  exact and_iff_right_of_imp fun h => (mem_neighbours x z).2 h.2.2.1

/-- The orientation used by `internalBonds`. -/
def edge (x z : Plane) : Plane × Plane :=
  if z ∈ positiveNeighbours x then (x, z) else (z, x)

theorem edge_cases (x z : Plane) : edge x z = (x, z) ∨ edge x z = (z, x) := by
  unfold edge
  split_ifs <;> simp

theorem edge_injective (x : Plane) : Function.Injective (edge x) := by
  intro z w h
  rcases edge_cases x z with hz | hz <;> rcases edge_cases x w with hw | hw <;>
    rw [hz, hw] at h <;> simp only [Prod.mk.injEq] at h
  all_goals simp_all

theorem edge_mem_bonds {G : Finset Plane} {D : Network G} {x z : Plane}
    (h : D.Present x z) : edge x z ∈ D.bonds := by
  have hxG := (Finset.mem_filter.mp h.1).1
  have hzG := (Finset.mem_filter.mp h.2.1).1
  unfold edge
  split_ifs with hp
  · exact Finset.mem_filter.mpr ⟨(mem_internal _ _).2 ⟨hxG, hp, hzG⟩, h⟩
  · have hp' := (adjacent_positive x z).mp h.2.2.1
    exact Finset.mem_filter.mpr
      ⟨(mem_internal _ _).2 ⟨hzG, hp'.resolve_left hp, hxG⟩, present_symm h⟩

theorem remove_active {G : Finset Plane} (D : Network G) (y : Plane) :
    (removeSite D y).active = D.active.erase y := by
  ext x
  simp only [Network.active, removeSite, Finset.mem_filter, Finset.mem_erase,
    Function.update_apply]
  by_cases h : x = y <;> simp [h]

theorem mem_remove_bonds {G : Finset Plane} (D : Network G) (y : Plane)
    (e : Plane × Plane) :
    e ∈ (removeSite D y).bonds ↔ e ∈ D.bonds ∧ e.1 ≠ y ∧ e.2 ≠ y := by
  unfold Network.bonds
  simp only [Finset.mem_filter]
  simp only [Network.Present, remove_active, Finset.mem_erase]
  change (e ∈ internalBonds G ∧ (e.1 ≠ y ∧ e.1 ∈ D.active) ∧
    (e.2 ≠ y ∧ e.2 ∈ D.active) ∧ Adjacent e.1 e.2 ∧ e.2 ∈ D.kept e.1 ∧
      e.1 ∈ D.kept e.2) ↔ _
  tauto

theorem incident_edge {G : Finset Plane} (D : Network G) (y : Plane)
    {e : Plane × Plane} (he : e ∈ D.bonds) (hi : e.1 = y ∨ e.2 = y) :
    ∃ z ∈ D.presentNeighbours y, e = edge y z := by
  have hp := (Finset.mem_filter.mp he).2
  have ho := (mem_internal G e).mp (Finset.mem_filter.mp he).1
  rcases e with ⟨x, z⟩
  rcases hi with rfl | rfl
  · exact ⟨z, (mem_presentNeighbours _ _ _).2 hp, by simp [edge, ho.2.1]⟩
  · exact ⟨x, (mem_presentNeighbours _ _ _).2 (present_symm hp),
      by simp [edge, positive_asymm ho.2.1]⟩

theorem bonds_split {G : Finset Plane} (D : Network G) (y : Plane) :
    D.bonds = (removeSite D y).bonds ∪ (D.presentNeighbours y).image (edge y) := by
  ext e
  constructor
  · intro he
    by_cases hi : e.1 = y ∨ e.2 = y
    · obtain ⟨z, hz, rfl⟩ := incident_edge D y he hi
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
    · exact Finset.mem_union_left _ ((mem_remove_bonds D y e).2
        ⟨he, not_or.mp hi⟩)
  · intro he
    rcases Finset.mem_union.mp he with he | he
    · exact ((mem_remove_bonds D y e).1 he).1
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp he
      exact edge_mem_bonds ((mem_presentNeighbours D y z).1 hz)

theorem bonds_split_disjoint {G : Finset Plane} (D : Network G) (y : Plane) :
    Disjoint (removeSite D y).bonds ((D.presentNeighbours y).image (edge y)) := by
  rw [Finset.disjoint_left]
  intro e he hi
  obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hi
  have hn := ((mem_remove_bonds D y _).1 he).2
  rcases edge_cases y z with h | h <;> simp_all

theorem no_original_leg {G : Finset Plane} {y : Plane} (hy : y ∉ protectedSites G)
    (e : originalLegs G) : e.val.1 ≠ y := by
  intro heq
  obtain ⟨x, hxG, hleg⟩ := Finset.mem_biUnion.mp e.property
  obtain ⟨z, hz, hze⟩ := Finset.mem_image.mp hleg
  obtain ⟨hzN, hzG⟩ := Finset.mem_sdiff.mp hz
  have hxy : x = y := (congrArg Prod.fst hze).trans heq
  rw [hxy] at hxG hzN
  have hd : latticeDist y z = 1 := (mem_neighbours y z).1 hzN
  apply hy
  apply Finset.mem_filter.mpr
  refine ⟨hxG, ?_⟩
  change (⨅ w : {w | w ∉ G}, (latticeDist y w.val : ℕ∞)) ≤ 2
  calc
    _ ≤ (latticeDist y z : ℕ∞) := iInf_le
      (fun w : {w | w ∉ G} => (latticeDist y w.val : ℕ∞)) ⟨z, hzG⟩
    _ ≤ 2 := by rw [hd]; norm_num

end AKLT.W.REC003
