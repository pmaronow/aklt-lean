module
public import AKLT.W.REC021.Moments

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC021

theorem neighbour_offsets (x y : Plane) : x ∈ neighbours y ↔
    x = y + (1, 0) ∨ x = y + (0, 1) ∨ x = y + (-1, 0) ∨ x = y + (0, -1) := by
  simp only [neighbours, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨d, rfl⟩
    cases d <;> simp [Compass.step]
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨.east, rfl⟩
    · exact ⟨.north, rfl⟩
    · exact ⟨.west, rfl⟩
    · exact ⟨.south, rfl⟩

theorem mem_neighbours_iff (x y : Plane) : x ∈ neighbours y ↔ Adjacent y x := by
  rw [neighbour_offsets]
  simp only [Adjacent, latticeDist, Prod.ext_iff, Prod.add_def]
  omega

theorem latticeDist_symm (x y : Plane) : latticeDist x y = latticeDist y x := by
  unfold latticeDist
  omega

theorem latticeDist_triangle (x y z : Plane) :
    latticeDist x z ≤ latticeDist x y + latticeDist y z := by
  have h1 := Int.natAbs_add_le (x.1 - y.1) (y.1 - z.1)
  have h2 := Int.natAbs_add_le (x.2 - y.2) (y.2 - z.2)
  have he1 : x.1 - y.1 + (y.1 - z.1) = x.1 - z.1 := by ring
  have he2 : x.2 - y.2 + (y.2 - z.2) = x.2 - z.2 := by ring
  rw [he1] at h1
  rw [he2] at h2
  unfold latticeDist
  omega

theorem neighbours_nonadjacent {y a b : Plane} (ha : a ∈ neighbours y)
    (hb : b ∈ neighbours y) : ¬ Adjacent a b := by
  rw [neighbour_offsets] at ha hb
  rcases ha with rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl <;>
    simp [Adjacent, latticeDist, Prod.add_def] <;> omega

theorem present_symm {G : Finset Plane} (D : Network G) {x y : Plane}
    (h : D.Present x y) : D.Present y x := by
  exact ⟨h.2.1, h.1, by simpa [Adjacent, latticeDist_symm] using h.2.2.1,
    h.2.2.2.2, h.2.2.2.1⟩

theorem active_remove {G : Finset Plane} (D : Network G) (y : Plane) :
    (removeSite D y).active = D.active.erase y := by
  ext x
  by_cases h : x = y
  · subst x; simp [Network.active, removeSite, Function.update_apply]
  · simp [Network.active, removeSite, h, Function.update_apply]

theorem present_remove {G : Finset Plane} (D : Network G) (y x z : Plane) :
    (removeSite D y).Present x z ↔ D.Present x z ∧ x ≠ y ∧ z ≠ y := by
  simp only [Network.Present]
  rw [active_remove]
  change (x ∈ D.active.erase y ∧ z ∈ D.active.erase y ∧ Adjacent x z ∧
    z ∈ D.kept x ∧ x ∈ D.kept z) ↔ _
  simp only [Finset.mem_erase]
  tauto

theorem neighbours_remove {G : Finset Plane} (D : Network G) (y x : Plane) (hxy : x ≠ y) :
    (removeSite D y).presentNeighbours x = (D.presentNeighbours x).erase y := by
  ext z
  simp only [Network.presentNeighbours, Finset.mem_filter, Finset.mem_erase, present_remove]
  tauto

theorem removed_neighbour_degree (a : AKLT.Blueprint.Rec.Departure)
    (x : Plane) (hx : x ∈ a.D.presentNeighbours a.y) :
    ((removeSite a.D a.y).presentNeighbours x).card ≤ 3 := by
  have hpx := (Finset.mem_filter.mp hx).2
  have hxy : x ≠ a.y := by
    intro h
    subst x
    have hh := hpx.2.2.1
    simp [Adjacent, latticeDist] at hh
  have hy : a.y ∈ a.D.presentNeighbours x := by
    apply Finset.mem_filter.mpr
    exact ⟨(mem_neighbours_iff _ _).mpr (present_symm a.D hpx).2.2.1,
      present_symm a.D hpx⟩
  have hd := a.auxiliary.1.2.2.2 x hpx.2.1
  rw [neighbours_remove a.D a.y x hxy, Finset.card_erase_of_mem hy]
  omega

theorem originalLeg_no_neighbour (a : AKLT.Blueprint.Rec.Departure)
    (x : Plane) (hx : x ∈ neighbours a.y) (e : originalLegs a.G) : e.val.1 ≠ x := by
  intro he
  rcases e with ⟨⟨ex, ez⟩, hm⟩
  dsimp at he
  simp only [originalLegs, Finset.mem_biUnion, Finset.mem_image, Finset.mem_sdiff,
    Prod.mk.injEq] at hm
  obtain ⟨v, hv, z, ⟨hz, hzg⟩, hvx, hze⟩ := hm
  have hev : v = x := hvx.trans he
  subst v
  rw [he] at hz
  have hdist : latticeDist a.y z ≤ 2 := by
    have hyx : latticeDist a.y x = 1 := (mem_neighbours_iff _ _).mp hx
    have hxz : latticeDist x z = 1 := (mem_neighbours_iff _ _).mp hz
    have ht := latticeDist_triangle a.y x z
    omega
  have hb : boundaryDepth a.G a.y ≤ 2 := by
    unfold boundaryDepth setDistance
    exact iInf_le_of_le ⟨z, hzg⟩ (by exact_mod_cast hdist)
  apply a.start.2.1
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp a.start.1).1, hb⟩

#print axioms removed_neighbour_degree
#print axioms originalLeg_no_neighbour

end AKLT.W.REC021
