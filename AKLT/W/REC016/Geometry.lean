module
public import AKLT.W.REC016.Analysis

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC016

theorem adjacent_symm {x y : Plane} (h : Adjacent x y) : Adjacent y x := by
  unfold Adjacent latticeDist at *
  rw [show y.1 - x.1 = -(x.1 - y.1) by ring,
    show y.2 - x.2 = -(x.2 - y.2) by ring]
  simpa only [Int.natAbs_neg] using h

theorem neighbour_adjacent {x y : Plane} (h : y ∈ neighbours x) : Adjacent x y := by
  obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp h
  cases d <;> simp [Adjacent, latticeDist, Compass.step]

theorem neighbours_card (x : Plane) : (neighbours x).card = 4 := by
  have hi : Function.Injective (fun d : Compass => x + d.step) := by
    intro d e h
    have he := add_left_cancel h
    cases d <;> cases e <;> simp_all [Compass.step]
  rw [neighbours, Finset.card_image_of_injective _ hi]
  rfl

theorem neighbours_nonadjacent {y x z : Plane}
    (hx : x ∈ neighbours y) (hz : z ∈ neighbours y) : ¬Adjacent x z := by
  obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hz
  cases d <;> cases e <;> simp [Adjacent, latticeDist, Compass.step]

theorem dist_triangle (x y z : Plane) :
    latticeDist x z ≤ latticeDist x y + latticeDist y z := by
  have h1 := Int.natAbs_add_le (x.1 - y.1) (y.1 - z.1)
  have h2 := Int.natAbs_add_le (x.2 - y.2) (y.2 - z.2)
  simp only [sub_add_sub_cancel] at h1 h2
  unfold latticeDist
  omega

theorem original_leg {G : Finset Plane} {e : Plane × Plane} (he : e ∈ originalLegs G) :
    e.1 ∈ G ∧ e.2 ∈ neighbours e.1 ∧ e.2 ∉ G := by
  obtain ⟨x, hx, hz⟩ := Finset.mem_biUnion.mp he
  obtain ⟨z', hz', heq⟩ := Finset.mem_image.mp hz
  cases heq
  exact ⟨hx, (Finset.mem_sdiff.mp hz').1, (Finset.mem_sdiff.mp hz').2⟩

theorem neighbour_no_leg {G : Finset Plane} {D : Network G} {y x : Plane}
    (hy : D.AdmissibleStart y) (hx : x ∈ neighbours y) :
    ∀ e ∈ originalLegs G, e.1 ≠ x := by
  intro e he h
  obtain ⟨_, hz, hout⟩ := original_leg he
  have hdist : latticeDist y e.2 ≤ 2 := by
    have h1 := neighbour_adjacent hx
    have h2 := neighbour_adjacent hz
    rw [h] at h2
    have htri := dist_triangle y x e.2
    unfold Adjacent at h1 h2
    omega
  have hyG : y ∈ G := (Finset.mem_filter.mp hy.1).1
  apply hy.2.1
  apply Finset.mem_filter.mpr
  refine ⟨hyG, ?_⟩
  have hdepth : boundaryDepth G y ≤ (latticeDist y e.2 : ℕ∞) :=
    iInf_le (fun z : {z : Plane // z ∉ G} => (latticeDist y z.val : ℕ∞)) ⟨e.2, hout⟩
  exact hdepth.trans (by exact_mod_cast hdist)

theorem removed_active {G : Finset Plane} (D : Network G) (y x : Plane) :
    x ∈ (removeSite D y).active ↔ x ∈ D.active ∧ x ≠ y := by
  classical
  by_cases h : x = y
  · subst x
    simp [Network.active, Finset.mem_filter, removeSite, Function.update]
  · simp [Network.active, Finset.mem_filter, removeSite, Function.update, h]

theorem present_symm {G : Finset Plane} {D : Network G} {x y : Plane}
    (h : D.Present x y) : D.Present y x :=
  ⟨h.2.1, h.1, adjacent_symm h.2.2.1, h.2.2.2.2, h.2.2.2.1⟩

theorem present_neighbour {G : Finset Plane} {D : Network G} (hD : D.LocalRules)
    {x y : Plane} (h : D.Present x y) : y ∈ D.presentNeighbours x := by
  exact Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp (hD.2.1 x h.2.2.2.1)).1, h⟩

theorem removed_degree {G : Finset Plane} {D : Network G} {y x : Plane}
    (hD : D.LocalRules) (hx : x ∈ D.presentNeighbours y) :
    ((removeSite D y).presentNeighbours x).card ≤ 3 := by
  have hp : D.Present y x := (Finset.mem_filter.mp hx).2
  have hyx : y ∈ neighbours x :=
    (Finset.mem_inter.mp (hD.2.1 x hp.2.2.2.2)).1
  have hsub : (removeSite D y).presentNeighbours x ⊆ (neighbours x).erase y := by
    intro z hz
    obtain ⟨hzn, hpz⟩ := Finset.mem_filter.mp hz
    refine Finset.mem_erase.mpr ⟨?_, hzn⟩
    exact ((removed_active D y z).mp hpz.2.1).2
  have hcard : ((neighbours x).erase y).card = 3 := by
    rw [Finset.card_erase_of_mem hyx, neighbours_card]
  exact (Finset.card_le_card hsub).trans_eq hcard

#print axioms neighbour_no_leg
#print axioms removed_degree

end AKLT.W.REC016
