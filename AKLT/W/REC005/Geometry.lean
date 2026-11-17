module
public import AKLT.W.REC005.Bounds

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

set_option maxHeartbeats 800000
set_option maxRecDepth 2000

namespace AKLT.W.REC005

lemma mem_neighbors (x z : Plane) : z ∈ neighbors x ↔ ∃ d : Compass, x + d.step = z := by
  simp [neighbors]

lemma dist_symm (x y : Plane) : latticeDist x y = latticeDist y x := by
  unfold latticeDist
  omega

lemma dist_triangle (x y z : Plane) : latticeDist x z ≤ latticeDist x y + latticeDist y z := by
  have h1 : x.1 - z.1 = (x.1 - y.1) + (y.1 - z.1) := by ring
  have h2 : x.2 - z.2 = (x.2 - y.2) + (y.2 - z.2) := by ring
  unfold latticeDist
  rw [h1, h2]
  have ha := Int.natAbs_add_le (x.1 - y.1) (y.1 - z.1)
  have hb := Int.natAbs_add_le (x.2 - y.2) (y.2 - z.2)
  omega

lemma neighbor_dist (x z : Plane) (hz : z ∈ neighbors x) : latticeDist x z = 1 := by
  obtain ⟨d, rfl⟩ := (mem_neighbors x z).mp hz
  cases d <;> simp [latticeDist, Compass.step]

lemma neighbors_nonadjacent (x a b : Plane) (ha : a ∈ neighbors x) (hb : b ∈ neighbors x) :
    ¬ Adjacent a b := by
  obtain ⟨d, rfl⟩ := (mem_neighbors x a).mp ha
  obtain ⟨e, rfl⟩ := (mem_neighbors x b).mp hb
  cases d <;> cases e <;> norm_num [Adjacent, latticeDist, Compass.step]

lemma adjacent_mem_neighbors (x z : Plane) (h : Adjacent x z) : z ∈ neighbors x := by
  have h1 : (x.1 - z.1).natAbs ≤ 1 := by unfold Adjacent latticeDist at h; omega
  have h2 : (x.2 - z.2).natAbs ≤ 1 := by unfold Adjacent latticeDist at h; omega
  have h1' : -1 ≤ x.1 - z.1 ∧ x.1 - z.1 ≤ 1 := by omega
  have h2' : -1 ≤ x.2 - z.2 ∧ x.2 - z.2 ≤ 1 := by omega
  apply (mem_neighbors x z).mpr
  have cases1 : x.1 - z.1 = -1 ∨ x.1 - z.1 = 0 ∨ x.1 - z.1 = 1 := by omega
  have cases2 : x.2 - z.2 = -1 ∨ x.2 - z.2 = 0 ∨ x.2 - z.2 = 1 := by omega
  rcases cases1 with h1 | h1 | h1 <;> rcases cases2 with h2 | h2 | h2
  all_goals
    simp only [Adjacent, latticeDist, h1, h2] at h
    norm_num at h
  · exact ⟨.east, by ext <;> simp [Compass.step] <;> omega⟩
  · exact ⟨.north, by ext <;> simp [Compass.step] <;> omega⟩
  · exact ⟨.south, by ext <;> simp [Compass.step] <;> omega⟩
  · exact ⟨.west, by ext <;> simp [Compass.step] <;> omega⟩

lemma neighbor_card (x : Plane) : (neighbors x).card = 4 := by
  unfold neighbors
  rw [Finset.card_image_of_injective]
  · decide
  · intro d e h
    have hstep : d.step = e.step := add_left_cancel h
    cases d <;> cases e <;> simp_all [Compass.step]

lemma originalLeg_mem {G : Finset Plane} (e : Plane × Plane) :
    e ∈ originalLegs G ↔ e.1 ∈ G ∧ e.2 ∈ neighbors e.1 ∧ e.2 ∉ G := by
  classical
  simp only [originalLegs, Finset.mem_biUnion, Finset.mem_image, Finset.mem_sdiff]
  constructor
  · rintro ⟨x, hx, z, hz, he⟩
    cases he
    exact ⟨hx, hz.1, hz.2⟩
  · rintro ⟨hx, hz, hn⟩
    exact ⟨e.1, hx, e.2, ⟨hz, hn⟩, rfl⟩

lemma no_neighbor_legs {G : Finset Plane} (D : Network G) (y x : Plane)
    (hy : y ∈ D.active) (hprotected : y ∉ protectedSites G) (hx : x ∈ neighbors y) :
    ∀ e ∈ originalLegs G, e.1 ≠ x := by
  intro e he hex
  obtain ⟨_, heN, heG⟩ := (originalLeg_mem e).mp he
  rw [hex] at heN
  have hd : latticeDist y e.2 ≤ 2 := by
    have ht := dist_triangle y x e.2
    rw [neighbor_dist y x hx, neighbor_dist x e.2 heN] at ht
    exact ht
  have hb : boundaryDepth G y ≤ 2 := by
    have hle : boundaryDepth G y ≤ (latticeDist y e.2 : ℕ∞) :=
      iInf_le (fun z : {z : Plane // z ∉ G} => (latticeDist y z : ℕ∞)) ⟨e.2, heG⟩
    exact hle.trans (by exact_mod_cast hd)
  apply hprotected
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).1, hb⟩

lemma removed_active {G : Finset Plane} (D : Network G) (y : Plane) :
    (removeSite D y).active = D.active.erase y := by
  classical
  ext x
  simp only [Network.active, Finset.mem_erase, Finset.mem_filter, removeSite]
  by_cases hxy : x = y
  · subst x
    simp [Function.update_apply]
  · simp [Function.update_apply, hxy]

lemma present_mem_active {G : Finset Plane} (D : Network G) {x z : Plane}
    (h : z ∈ D.presentNeighbors x) : x ∈ D.active ∧ z ∈ D.active ∧ z ∈ neighbors x := by
  obtain ⟨hz, hp⟩ := Finset.mem_filter.mp h
  exact ⟨hp.1, hp.2.1, hz⟩

end AKLT.W.REC005
