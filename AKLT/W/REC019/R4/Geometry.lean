import AKLT.W.REC019.R4.Algebra

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC019.R4

lemma latticeDist_comm (x y : Plane) : latticeDist x y = latticeDist y x := by
  unfold latticeDist
  omega

lemma latticeDist_triangle (x y z : Plane) :
    latticeDist x z ≤ latticeDist x y + latticeDist y z := by
  unfold latticeDist
  have h1 := Int.natAbs_add_le (x.1 - y.1) (y.1 - z.1)
  have h2 := Int.natAbs_add_le (x.2 - y.2) (y.2 - z.2)
  simp only [sub_add_sub_cancel] at h1 h2
  omega

lemma adjacent_iff (x y : Plane) : Adjacent x y ↔
    y = x + Compass.east.step ∨ y = x + Compass.north.step ∨
    y = x + Compass.west.step ∨ y = x + Compass.south.step := by
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  simp only [Adjacent, latticeDist, Compass.step, Prod.mk_add_mk, Prod.mk.injEq]
  omega

lemma mem_neighbours_iff (x y : Plane) : y ∈ neighbours x ↔ Adjacent x y := by
  simp only [neighbours, Finset.mem_image, Finset.mem_univ, true_and]
  rw [adjacent_iff]
  constructor
  · rintro ⟨d, rfl⟩
    cases d <;> tauto
  · rintro (h | h | h | h)
    · exact ⟨.east, h.symm⟩
    · exact ⟨.north, h.symm⟩
    · exact ⟨.west, h.symm⟩
    · exact ⟨.south, h.symm⟩

lemma adjacent_ne (x y : Plane) (h : Adjacent x y) : x ≠ y := by
  intro he
  subst y
  norm_num [Adjacent, latticeDist] at h

lemma neighbours_nonadjacent (y f g : Plane)
    (hf : Adjacent y f) (hg : Adjacent y g) : ¬ Adjacent f g := by
  rcases (adjacent_iff y f).1 hf with rfl | rfl | rfl | rfl <;>
    rcases (adjacent_iff y g).1 hg with rfl | rfl | rfl | rfl <;>
    simp [Adjacent, latticeDist, Compass.step]

lemma originalLeg_mem {G : Finset Plane} {e : Plane × Plane}
    (he : e ∈ originalLegs G) : e.1 ∈ G ∧ e.2 ∉ G ∧ Adjacent e.1 e.2 := by
  simp only [originalLegs, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_sdiff] at he
  rcases he with ⟨x, hx, z, ⟨hz, hzG⟩, rfl⟩
  exact ⟨hx, hzG, (mem_neighbours_iff x z).1 hz⟩

lemma no_leg_at_neighbour {G : Finset Plane} {D : Network G} {y f : Plane}
    (hy : D.AdmissibleStart y) (hf : f ∈ D.presentNeighbours y) :
    ∀ e ∈ originalLegs G, e.1 ≠ f := by
  intro e he hef
  have hyG : y ∈ G := (Finset.mem_filter.1 hy.1).1
  have hyP := hy.2.1
  have hyDepth : ¬ boundaryDepth G y ≤ 2 := by
    intro h
    exact hyP (Finset.mem_filter.2 ⟨hyG, h⟩)
  have hfAdj := (Finset.mem_filter.1 hf).2.2.2.1
  obtain ⟨_, hz, hAdj⟩ := originalLeg_mem he
  rw [hef] at hAdj
  have hdist : latticeDist y e.2 ≤ 2 := by
    have ht := latticeDist_triangle y f e.2
    change latticeDist y f = 1 at hfAdj
    change latticeDist f e.2 = 1 at hAdj
    omega
  apply hyDepth
  apply le_trans (iInf_le (fun z : {z : Plane | z ∉ G} =>
    (latticeDist y z : ℕ∞)) ⟨e.2, hz⟩)
  exact_mod_cast hdist

lemma present_symm {G : Finset Plane} {D : Network G} {x y : Plane}
    (h : D.Present x y) : D.Present y x := by
  exact ⟨h.2.1, h.1, by simpa [Adjacent, latticeDist_comm] using h.2.2.1,
    h.2.2.2.2, h.2.2.2.1⟩

lemma present_mem_neighbours {G : Finset Plane} {D : Network G} {x y : Plane}
    (h : D.Present x y) : y ∈ D.presentNeighbours x := by
  exact Finset.mem_filter.2 ⟨(mem_neighbours_iff x y).2 h.2.2.1, h⟩

lemma remove_neighbours {G : Finset Plane} (D : Network G) {x y : Plane} (hxy : x ≠ y) :
    (removeSite D y).presentNeighbours x = (D.presentNeighbours x).erase y := by
  ext z
  by_cases hzy : z = y
  · subst z
    simp [Network.presentNeighbours, Network.Present, Network.active, removeSite,
      Function.update_apply, Finset.mem_filter]
  · simp [Network.presentNeighbours, Network.Present, Network.active, removeSite,
      Function.update_apply, hxy, hzy]

lemma neighbour_removed_card {G : Finset Plane} {D : Network G} {y f : Plane}
    (hD : D.Auxiliary) (hf : f ∈ D.presentNeighbours y) :
    ((removeSite D y).presentNeighbours f).card ≤ 3 := by
  have hp := (Finset.mem_filter.1 hf).2
  have hfy : f ≠ y := (adjacent_ne y f hp.2.2.1).symm
  have hy : y ∈ D.presentNeighbours f := present_mem_neighbours (present_symm hp)
  have hcard := hD.1.2.2.2 f hp.2.1
  rw [remove_neighbours D hfy, Finset.card_erase_of_mem hy]
  omega

lemma neighbour_survives {G : Finset Plane} {D : Network G} {y f : Plane}
    (hf : f ∈ D.presentNeighbours y) :
    f ∈ (removeSite D y).active ∧
      ((removeSite D y).status f = .U ∨ (removeSite D y).status f = .D) := by
  have hp := (Finset.mem_filter.1 hf).2
  have hfy : f ≠ y := (adjacent_ne y f hp.2.2.1).symm
  have ha := Finset.mem_filter.1 hp.2.1
  have hstatus : (removeSite D y).status f = D.status f := by
    simp [removeSite, hfy]
  constructor
  · simp [Network.active, hstatus, ha]
  · rw [hstatus]
    cases h : D.status f <;> simp_all


end AKLT.W.REC019.R4
