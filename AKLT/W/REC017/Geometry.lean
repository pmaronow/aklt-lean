import AKLT.W.REC017.Quadrature

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC017

theorem adjacent_symm {x y : Plane} (h : Adjacent x y) : Adjacent y x := by
  unfold Adjacent latticeDist at *
  rw [show y.1 - x.1 = -(x.1 - y.1) by ring,
    show y.2 - x.2 = -(x.2 - y.2) by ring, Int.natAbs_neg, Int.natAbs_neg]
  exact h

theorem positive_ne (x y : Plane) (h : y ∈ positiveNeighbours x) : x ≠ y := by
  simp only [positiveNeighbours, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h <;> intro he <;>
    have hs := congrArg (fun p : Plane => p.1 + p.2) h <;>
    have ht := congrArg (fun p : Plane => p.1 + p.2) he <;> dsimp at hs ht <;> omega

theorem positive_no_reverse (x y : Plane) (h : y ∈ positiveNeighbours x) :
    x ∉ positiveNeighbours y := by
  simp only [positiveNeighbours, Finset.mem_insert, Finset.mem_singleton] at *
  rcases h with h | h <;> rcases h with rfl <;> intro he <;>
    rcases he with he | he <;>
    have he := congrArg (fun p : Plane => p.1 + p.2) he <;> dsimp at he <;> omega

theorem positive_neighbour {x y : Plane} (h : y ∈ positiveNeighbours x) :
    y ∈ neighbours x := by
  simp only [positiveNeighbours, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl
  · exact Finset.mem_image.mpr ⟨.east, Finset.mem_univ _, by ext <;> simp [Compass.step]⟩
  · exact Finset.mem_image.mpr ⟨.north, Finset.mem_univ _, by ext <;> simp [Compass.step]⟩

theorem reverse_positive_neighbour {x y : Plane} (h : y ∈ positiveNeighbours x) :
    x ∈ neighbours y := by
  simp only [positiveNeighbours, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl
  · exact Finset.mem_image.mpr ⟨.west, Finset.mem_univ _, by ext <;> simp [Compass.step]⟩
  · exact Finset.mem_image.mpr ⟨.south, Finset.mem_univ _, by ext <;> simp [Compass.step]⟩

theorem neighbour_orientation {x y : Plane} (h : y ∈ neighbours x) :
    y ∈ positiveNeighbours x ∨ x ∈ positiveNeighbours y := by
  rcases Finset.mem_image.mp h with ⟨d, hd, rfl⟩
  cases d <;> simp [positiveNeighbours, Compass.step, Prod.add_def]

theorem neighbour_adjacent {x y : Plane} (h : y ∈ neighbours x) : Adjacent x y := by
  rcases Finset.mem_image.mp h with ⟨d, hd, rfl⟩
  cases d <;> simp [Adjacent, latticeDist, Compass.step, Prod.add_def]

theorem present_symm {G : Finset Plane} {D : Network G} {x y : Plane}
    (h : D.Present x y) : D.Present y x :=
  ⟨h.2.1, h.1, adjacent_symm h.2.2.1, h.2.2.2.2, h.2.2.2.1⟩

theorem mem_internal {G : Finset Plane} {e : Plane × Plane} :
    e ∈ internalBonds G ↔ e.1 ∈ G ∧ e.2 ∈ positiveNeighbours e.1 ∧ e.2 ∈ G := by
  simp only [internalBonds, Finset.mem_biUnion, Finset.mem_image, Finset.mem_inter]
  constructor
  · rintro ⟨x, hx, z, ⟨hz, hzg⟩, he⟩
    subst e
    exact ⟨hx, hz, hzg⟩
  · rintro ⟨hx, hz, hzg⟩
    exact ⟨e.1, hx, e.2, ⟨hz, hzg⟩, rfl⟩

theorem mem_bonds {G : Finset Plane} {D : Network G} {e : Plane × Plane} :
    e ∈ D.bonds ↔ e.2 ∈ positiveNeighbours e.1 ∧ D.Present e.1 e.2 := by
  simp only [Network.bonds, Finset.mem_filter, mem_internal]
  constructor
  · exact fun h => ⟨h.1.2.1, h.2⟩
  · intro h
    exact ⟨⟨(Finset.mem_filter.mp h.2.1).1, h.1,
      (Finset.mem_filter.mp h.2.2.1).1⟩, h.2⟩

theorem no_leg_at_start {G : Finset Plane} {D : Network G} {y : Plane}
    (hy : D.AdmissibleStart y) (e : originalLegs G) : e.val.1 ≠ y := by
  intro he
  have hm := e.property
  simp only [originalLegs, Finset.mem_biUnion, Finset.mem_image, Finset.mem_sdiff] at hm
  rcases hm with ⟨x, hx, z, ⟨hz, hzg⟩, heq⟩
  have hxy : x = y := by simpa [← heq] using he
  subst x
  have hd : boundaryDepth G y ≤ (1 : ℕ∞) := by
    unfold boundaryDepth setDistance
    exact iInf_le_of_le ⟨z, hzg⟩ (by rw [neighbour_adjacent hz]; exact le_rfl)
  apply hy.2.1
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy.1).1, hd.trans (by norm_num)⟩

end AKLT.W.REC017
