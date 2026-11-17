module
public import AKLT.Blueprint.Rec.NodesResponse

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC019

theorem latticeDist_triangle (x y z : Plane) :
    latticeDist x z ≤ latticeDist x y + latticeDist y z := by
  have h1 := Int.natAbs_add_le (x.1 - y.1) (y.1 - z.1)
  have h2 := Int.natAbs_add_le (x.2 - y.2) (y.2 - z.2)
  simp only [sub_add_sub_cancel] at h1 h2
  unfold latticeDist
  omega

theorem adjacent_symmetric {x y : Plane} (h : Adjacent x y) : Adjacent y x := by
  unfold Adjacent latticeDist at h ⊢
  have h1 : (y.1 - x.1).natAbs = (x.1 - y.1).natAbs := by omega
  have h2 : (y.2 - x.2).natAbs = (x.2 - y.2).natAbs := by omega
  rwa [h1, h2]

theorem adjacent_of_mem_neighbours {x y : Plane} (h : y ∈ neighbours x) :
    Adjacent x y := by
  rcases Finset.mem_image.mp h with ⟨d, hd, rfl⟩
  cases d <;> dsimp [Compass.step, Adjacent, latticeDist] <;> omega

theorem neighbours_nonadjacent {x f g : Plane}
    (hf : f ∈ neighbours x) (hg : g ∈ neighbours x) : ¬ Adjacent f g := by
  rcases Finset.mem_image.mp hf with ⟨d, hd, rfl⟩
  rcases Finset.mem_image.mp hg with ⟨e, he, rfl⟩
  cases d <;> cases e <;> dsimp [Compass.step, Adjacent, latticeDist] <;> omega

theorem interior_distance {G : Finset Plane} {y : Plane}
    (hy : y ∈ G) (hi : y ∉ protectedSites G) {z : Plane} (hz : z ∉ G) :
    2 < latticeDist y z := by
  have hd : ¬ boundaryDepth G y ≤ 2 := by
    intro h
    exact hi (Finset.mem_filter.mpr ⟨hy, h⟩)
  by_contra h
  apply hd
  have hle : boundaryDepth G y ≤ (latticeDist y z : ℕ∞) :=
    iInf_le (fun w : {z | z ∉ G} => (latticeDist y w.val : ℕ∞)) ⟨z, hz⟩
  apply hle.trans
  exact_mod_cast (show latticeDist y z ≤ 2 by omega)

/-- A neighbor of an admissible departure has no original pin factor. -/
theorem departure_neighbour_no_leg (a : Departure) {x : Plane}
    (hx : x ∈ a.D.presentNeighbours a.y) :
    ∀ e ∈ originalLegs a.G, e.1 ≠ x := by
  have hxy := adjacent_of_mem_neighbours (Finset.mem_filter.mp hx).1
  intro e he hex
  rcases Finset.mem_biUnion.mp he with ⟨u, hu, he⟩
  rcases Finset.mem_image.mp he with ⟨z, hz, heq⟩
  have hu' : u = x := by simpa [← heq] using hex
  have hzx := adjacent_of_mem_neighbours (Finset.mem_sdiff.mp hz).1
  have hzg := (Finset.mem_sdiff.mp hz).2
  rw [hu'] at hzx
  have hdist := interior_distance (Finset.mem_filter.mp a.start.1).1 a.start.2.1 hzg
  have htri := latticeDist_triangle a.y x z
  unfold Adjacent at hxy hzx
  omega

theorem remove_presentNeighbours {G : Finset Plane} (D : Network G)
    (y x : Plane) (hxy : x ≠ y) :
    (removeSite D y).presentNeighbours x = (D.presentNeighbours x).erase y := by
  ext z
  by_cases hz : z = y
  · subst z
    simp [Network.presentNeighbours, Finset.mem_filter, Network.Present, Network.active,
      removeSite, Function.update_apply]
  · simp [Network.presentNeighbours, Finset.mem_filter, Network.Present, Network.active,
      removeSite, Function.update_apply, hxy, hz]

theorem present_symmetric {G : Finset Plane} (D : Network G) {x y : Plane}
    (h : D.Present x y) : D.Present y x :=
  ⟨h.2.1, h.1, adjacent_symmetric h.2.2.1, h.2.2.2.2, h.2.2.2.1⟩

theorem departure_neighbour_removed_degree (a : Departure) {x : Plane}
    (hx : x ∈ a.D.presentNeighbours a.y) :
    ((removeSite a.D a.y).presentNeighbours x).card ≤ 3 := by
  have hpres := (Finset.mem_filter.mp hx).2
  have hxy : x ≠ a.y := by
    intro h
    have hadj := hpres.2.2.1
    rw [h] at hadj
    simp [Adjacent, latticeDist] at hadj
  have hrev := present_symmetric a.D hpres
  have hmem : a.y ∈ a.D.presentNeighbours x := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, hrev⟩
    rcases Finset.mem_image.mp (Finset.mem_filter.mp hx).1 with ⟨d, hd, he⟩
    apply Finset.mem_image.mpr
    refine ⟨d.reverse, Finset.mem_univ _, ?_⟩
    rw [← he]
    cases d <;> ext <;> simp [Compass.reverse, Compass.step]
  rw [remove_presentNeighbours _ _ _ hxy, Finset.card_erase_of_mem hmem]
  have hdeg := a.auxiliary.1.2.2.2 x hpres.2.1
  omega

end AKLT.W.REC019
