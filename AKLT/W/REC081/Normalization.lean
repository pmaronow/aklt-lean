module
public import AKLT.W.REC081.Geometry

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC081

theorem normalized_kept_subset (p : PairData) (x : Plane) :
    p.normalized.kept x ⊆ p.D.kept x := by
  change (if x = p.u ∧ p.D.status p.u = .U then (p.D.kept x).erase p.c
    else p.D.kept x) ⊆ p.D.kept x
  split
  · exact Finset.erase_subset _ _
  · exact Finset.Subset.refl _

/-- Erasing a flag to the removed center changes no present bond. -/
theorem normalized_present_iff (p : PairData) (x y : Plane) :
    p.normalized.Present x y ↔ p.D.Present x y := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1, h.2.2.1, normalized_kept_subset p x h.2.2.2.1,
      normalized_kept_subset p y h.2.2.2.2⟩
  · intro h
    have hxc : x ≠ p.c := by
      intro heq
      have hx := (Finset.mem_filter.mp h.1).2
      rw [heq] at hx
      exact hx p.pair.2.2.2.2.1
    have hyc : y ≠ p.c := by
      intro heq
      have hy := (Finset.mem_filter.mp h.2.1).2
      rw [heq] at hy
      exact hy p.pair.2.2.2.2.1
    refine ⟨h.1, h.2.1, h.2.2.1, ?_, ?_⟩
    · change y ∈ if x = p.u ∧ p.D.status p.u = .U then (p.D.kept x).erase p.c
        else p.D.kept x
      split
      · exact Finset.mem_erase.mpr ⟨hyc, h.2.2.2.1⟩
      · exact h.2.2.2.1
    · change x ∈ if y = p.u ∧ p.D.status p.u = .U then (p.D.kept y).erase p.c
        else p.D.kept y
      split
      · exact Finset.mem_erase.mpr ⟨hxc, h.2.2.2.2⟩
      · exact h.2.2.2.2

theorem normalized_presentNeighbors (p : PairData) (x : Plane) :
    p.normalized.presentNeighbors x = p.D.presentNeighbors x := by
  ext y
  simp only [Network.presentNeighbors, Finset.mem_filter, normalized_present_iff]

theorem normalized_auxiliary (p : PairData) : p.normalized.Auxiliary := by
  obtain ⟨hcons, _, _, _, _, _, _, _, _, _⟩ := p.pair
  have hlocal := hcons.1.1
  refine ⟨⟨hlocal.1, ?_, ?_, ?_⟩, ?_⟩
  · intro x
    exact (normalized_kept_subset p x).trans (hlocal.2.1 x)
  · intro x hx hD
    rw [normalized_presentNeighbors]
    exact hlocal.2.2.1 x hx hD
  · intro x hx
    rw [normalized_presentNeighbors]
    exact hlocal.2.2.2 x hx
  · intro x hx
    exact (hcons.1.2 x hx).1

theorem adjacent_mem_neighbors (x y : Plane) (h : Adjacent x y) : y ∈ neighbors x := by
  have hsym : Adjacent y x := by
    unfold Adjacent latticeDist at h ⊢
    omega
  obtain ⟨incoming, hin⟩ := adjacent_compass y x hsym
  exact Finset.mem_image.mpr ⟨incoming, Finset.mem_univ _, hin.symm⟩

theorem neighbors_card_le (x : Plane) : (neighbors x).card ≤ 4 := by
  exact (Finset.card_image_le).trans (by decide : Finset.univ.card ≤ 4)

theorem normalized_start (p : PairData) (hinterior : p.u ∉ protectedSites p.G) :
    p.normalized.AdmissibleStart p.u := by
  obtain ⟨_, hu, _, _, hc, huc, _, _, hcases, _⟩ := p.pair
  refine ⟨hu, hinterior, ?_⟩
  rw [normalized_presentNeighbors]
  rcases hcases with hU | hD
  · refine Or.inl ⟨hU, ?_⟩
    have hnot : p.c ∉ p.D.presentNeighbors p.u := by
      intro h
      have hcactive := ((Finset.mem_filter.mp h).2).2.1
      exact (Finset.mem_filter.mp hcactive).2 hc
    have hsub : insert p.c (p.D.presentNeighbors p.u) ⊆ neighbors p.u := by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact adjacent_mem_neighbors _ _ huc
      · exact (Finset.mem_filter.mp hy).1
    have hcard := (Finset.card_le_card hsub).trans (neighbors_card_le p.u)
    rw [Finset.card_insert_of_notMem hnot] at hcard
    omega
  · exact Or.inr hD

theorem pairSetup_of_interior (p : PairData) (hu : p.u ∉ protectedSites p.G) :
    ∃ setup : PairSetup, setup.toPairData = p := by
  obtain ⟨incoming, hin⟩ := adjacent_compass p.u p.c p.pair.2.2.2.2.2.1
  exact ⟨⟨p, incoming, hin, hu⟩, rfl⟩

end AKLT.W.REC081
