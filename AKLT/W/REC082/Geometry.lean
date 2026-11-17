module
public import AKLT.W.REC082.Normalization

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC082

/-- The four directions enumerate precisely the ambient nearest neighbors. -/
theorem adjacent_iff_mem_neighbours (x y : Plane) : Adjacent x y ↔ y ∈ neighbours x := by
  classical
  constructor
  · intro h
    have he : (y.1 = x.1 + 1 ∧ y.2 = x.2) ∨ (y.1 = x.1 - 1 ∧ y.2 = x.2) ∨
        (y.1 = x.1 ∧ y.2 = x.2 + 1) ∨ (y.1 = x.1 ∧ y.2 = x.2 - 1) := by
      unfold Adjacent latticeDist at h
      omega
    simp only [neighbours, Finset.mem_image, Finset.mem_univ, true_and]
    rcases he with he | he | he | he
    · exact ⟨.east, by ext <;> simp_all [Compass.step]⟩
    · exact ⟨.west, by ext <;> simp_all [Compass.step, sub_eq_add_neg]⟩
    · exact ⟨.north, by ext <;> simp_all [Compass.step]⟩
    · exact ⟨.south, by ext <;> simp_all [Compass.step, sub_eq_add_neg]⟩
  · simp only [neighbours, Finset.mem_image, Finset.mem_univ, true_and]
    rintro ⟨d, rfl⟩
    cases d <;> simp [Adjacent, latticeDist, Compass.step]

theorem neighbours_card (x : Plane) : (neighbours x).card = 4 := by
  classical
  rw [neighbours, Finset.card_image_of_injective]
  · rfl
  · intro a b h
    have hs : a.step = b.step := add_left_cancel h
    cases a <;> cases b <;> simp_all [Compass.step]

theorem neighbours_degree_of_removed {G : Finset Plane} (D : Network G)
    {u c : Plane} (hc : D.status c = .X) (huc : Adjacent u c) :
    (D.presentNeighbours u).card ≤ 3 := by
  classical
  have hs : D.presentNeighbours u ⊆ (neighbours u).erase c := by
    intro z hz
    obtain ⟨hn, hp⟩ := Finset.mem_filter.mp hz
    have hzc : z ≠ c := by
      intro h
      exact removed_not_active D hc (h ▸ hp.2.1)
    exact Finset.mem_erase.mpr ⟨hzc, hn⟩
  have hcard := Finset.card_le_card hs
  rw [Finset.card_erase_of_mem ((adjacent_iff_mem_neighbours u c).mp huc),
    neighbours_card] at hcard
  exact hcard

/-- An unprotected site carries no original leg. -/
theorem no_originalLegs {G : Finset Plane} {x : Plane} (hx : x ∉ protectedSites G) :
    ((originalLegs G).filter fun e => e.1 = x) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨he, hex⟩ := Finset.mem_filter.mp he
  obtain ⟨y, hyG, he⟩ := Finset.mem_biUnion.mp he
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp he
  have hyx : y = x := hex
  subst x
  have hz' : z ∈ neighbours y \ G := by simpa using hz
  have hnot : z ∉ G := (Finset.mem_sdiff.mp hz').2
  have hadj : Adjacent y z :=
    (adjacent_iff_mem_neighbours y z).mpr (Finset.mem_sdiff.mp hz').1
  apply hx
  simp only [protectedSites, Finset.mem_filter]
  refine ⟨hyG, ?_⟩
  have hdist : boundaryDepth G y ≤ (latticeDist y z : ℕ∞) :=
    iInf_le_of_le ⟨z, hnot⟩ le_rfl
  rw [show latticeDist y z = 1 from hadj] at hdist
  exact hdist.trans (by norm_num)

theorem pair_ne (p : PairData) : p.u ≠ p.v := by
  have hd := p.pair.2.2.2.2.2.2.2.1.1
  intro h
  simp [h, latticeDist] at hd

theorem pair_start (p : PairData) (hu : p.u ∉ protectedSites p.G) :
    p.D.AdmissibleStart p.u := by
  refine ⟨pair_u_active p, hu, ?_⟩
  rcases p.pair.2.2.2.2.2.2.2.2.1 with hU | hD
  · exact Or.inl ⟨hU, neighbours_degree_of_removed p.D (pair_c_removed p)
      p.pair.2.2.2.2.2.1⟩
  · exact Or.inr hD

theorem pair_target (p : PairData) (hv : p.v ∉ protectedSites p.G) :
    AdmissibleTarget p.D p.v := by
  refine ⟨pair_v_active p, ?_⟩
  rcases p.pair.2.2.2.2.2.2.2.2.2 with hU | hD
  · left
    refine ⟨hU, ?_⟩
    rw [no_originalLegs hv, Finset.card_empty, add_zero]
    exact neighbours_degree_of_removed p.D (pair_c_removed p) p.pair.2.2.2.2.2.2.1
  · exact Or.inr hD

theorem normalized_start (p : PairData) (hu : p.u ∉ protectedSites p.G) :
    p.normalized.AdmissibleStart p.u := by
  have h := pair_start p hu
  simpa only [Network.AdmissibleStart,
    show p.normalized.active = p.D.active from rfl,
    show p.normalized.status = p.D.status from rfl,
    show p.normalized.presentNeighbours p.u = p.D.presentNeighbours p.u from
      normalizeStart_presentNeighbours p.D p.u p.c p.u (pair_c_removed p)] using h

theorem normalized_target (p : PairData) (hv : p.v ∉ protectedSites p.G) :
    AdmissibleTarget p.normalized p.v := by
  have h := pair_target p hv
  simpa only [AdmissibleTarget,
    show p.normalized.active = p.D.active from rfl,
    show p.normalized.status = p.D.status from rfl,
    show p.normalized.presentNeighbours p.v = p.D.presentNeighbours p.v from
      normalizeStart_presentNeighbours p.D p.u p.c p.v (pair_c_removed p)] using h

end AKLT.W.REC082
