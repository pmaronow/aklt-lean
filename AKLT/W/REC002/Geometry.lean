import AKLT.W.REC002.Moments

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC002

theorem adjacent_symm (x y : Plane) : Adjacent x y ↔ Adjacent y x := by
  simp only [Adjacent, latticeDist]
  omega

theorem adjacent_ne {x y : Plane} (h : Adjacent x y) : x ≠ y := by
  rintro rfl
  norm_num [Adjacent, latticeDist] at h

theorem adjacent_iff_positive (x y : Plane) :
    Adjacent x y ↔ y ∈ positiveNeighbours x ∨ x ∈ positiveNeighbours y := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  simp only [Adjacent, latticeDist, positiveNeighbours, Finset.mem_insert,
    Finset.mem_singleton, Prod.mk.injEq]
  omega

theorem neighbour_iff (x y : Plane) : y ∈ neighbours x ↔ Adjacent x y := by
  rw [adjacent_iff_positive]
  simp only [neighbours, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨d, rfl⟩
    fin_cases d <;> simp [positiveNeighbours, Compass.step, Prod.ext_iff]
  · intro h
    simp only [positiveNeighbours, Finset.mem_insert, Finset.mem_singleton,
      Prod.ext_iff] at h
    rcases h with (h | h) | (h | h)
    · exact ⟨.east, by simpa [Compass.step, Prod.ext_iff] using ⟨h.1.symm, h.2.symm⟩⟩
    · exact ⟨.north, by simpa [Compass.step, Prod.ext_iff] using ⟨h.1.symm, h.2.symm⟩⟩
    · refine ⟨.west, ?_⟩
      simp [Compass.step, Prod.ext_iff] at *
      omega
    · refine ⟨.south, ?_⟩
      simp [Compass.step, Prod.ext_iff] at *
      omega

theorem present_symm {G : Finset Plane} (D : Network G) (x y : Plane) :
    D.Present x y ↔ D.Present y x := by
  simp only [Network.Present, adjacent_symm x y]
  tauto

theorem present_ne {G : Finset Plane} {D : Network G} {x y : Plane}
    (h : D.Present x y) : x ≠ y := adjacent_ne h.2.2.1

theorem mem_presentNeighbours {G : Finset Plane} (D : Network G) (x y : Plane) :
    y ∈ D.presentNeighbours x ↔ D.Present x y := by
  simp only [Network.presentNeighbours, Finset.mem_filter, neighbour_iff]
  exact ⟨And.right, fun h => ⟨h.2.2.1, h⟩⟩

theorem mem_internal (G : Finset Plane) (x y : Plane) :
    (x, y) ∈ internalBonds G ↔ x ∈ G ∧ y ∈ G ∧ y ∈ positiveNeighbours x := by
  simp [internalBonds, and_comm, and_left_comm, and_assoc]

theorem mem_bonds {G : Finset Plane} (D : Network G) (x y : Plane) :
    (x, y) ∈ D.bonds ↔ D.Present x y ∧ y ∈ positiveNeighbours x := by
  simp only [Network.bonds, Finset.mem_filter, mem_internal]
  constructor
  · tauto
  · intro h
    exact ⟨⟨(Finset.mem_filter.mp h.1.1).1,
      (Finset.mem_filter.mp h.1.2.1).1, h.2⟩, h.1⟩

theorem remove_active {G : Finset Plane} (D : Network G) (y : Plane) :
    (removeSite D y).active = D.active.erase y := by
  ext x
  by_cases h : x = y <;> simp [Network.active, removeSite, Function.update_apply, h]

theorem mem_remove_active {G : Finset Plane} (D : Network G) (y x : Plane) :
    x ∈ (removeSite D y).active ↔ x ∈ D.active ∧ x ≠ y := by
  rw [remove_active, Finset.mem_erase]
  tauto

theorem remove_bonds {G : Finset Plane} (D : Network G) (y : Plane) :
    (removeSite D y).bonds = D.bonds.filter (fun e => e.1 ≠ y ∧ e.2 ≠ y) := by
  ext ⟨x, z⟩
  simp only [mem_bonds, Network.Present, mem_remove_active,
    Finset.mem_filter]
  simp only [removeSite]
  tauto

theorem no_leg {G : Finset Plane} {D : Network G} {y : Plane}
    (hy : D.AdmissibleStart y) (e : originalLegs G) : e.val.1 ≠ y := by
  intro h
  have he := e.property
  simp only [originalLegs, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_sdiff] at he
  obtain ⟨x, hx, z, ⟨hz, hzout⟩, heq⟩ := he
  have hxy : x = y := (congrArg Prod.fst heq).trans h
  subst x
  have hd : boundaryDepth G y ≤ 2 := by
    have hz' : latticeDist y z = 1 := (neighbour_iff y z).mp hz
    unfold boundaryDepth setDistance
    exact iInf_le_of_le ⟨z, hzout⟩ (by simpa only [hz', Nat.cast_one] using
      (show (1 : ℕ∞) ≤ 2 by norm_num))
  exact hy.2.1 (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy.1).1, hd⟩)

end AKLT.W.REC002
