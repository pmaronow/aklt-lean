module
public import AKLT.W.REC096.Main
public import AKLT.W.REC039.Main
public import AKLT.W.REC050.Main
public import AKLT.W.REC079.TraceGeometry

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC079

open AKLT.W.REC096

theorem remove_active {G : Finset Plane} (E : Network G) (y : Plane) :
    (removeSite E y).active = E.active.erase y := by
  classical
  ext x
  simp only [Network.active, removeSite, Finset.mem_filter, Finset.mem_erase]
  by_cases h : x = y <;> simp [Function.update_apply, h, and_comm]

theorem remove_present {G : Finset Plane} (E : Network G) (y x z : Plane) :
    (removeSite E y).Present x z ↔ E.Present x z ∧ x ≠ y ∧ z ≠ y := by
  rw [Network.Present, remove_active]
  simp only [Finset.mem_erase, removeSite, Network.Present]
  tauto

theorem remove_auxiliary {G : Finset Plane} (E : Network G) (y : Plane)
    (hE : E.Auxiliary) (hS : y ∉ protectedSites G) : (removeSite E y).Auxiliary := by
  classical
  have hsub (x : Plane) : (removeSite E y).presentNeighbors x ⊆ E.presentNeighbors x := by
    intro z hz
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,
      ((remove_present E y x z).mp (Finset.mem_filter.mp hz).2).1⟩
  refine ⟨⟨?_, hE.1.2.1, ?_, ?_⟩, ?_⟩
  · intro x hx
    by_cases hxy : x = y
    · simp [removeSite, hxy]
    · simpa [removeSite, hxy] using hE.1.1 x hx
  · intro x hx hd
    have hxy : x ≠ y := by rintro rfl; simp [removeSite] at hd
    have hd' : E.status x = .D := by simpa [removeSite, hxy] using hd
    exact (Finset.card_le_card (hsub x)).trans (hE.1.2.2.1 x hx hd')
  · intro x hx
    have hx' : x ∈ E.active := Finset.mem_of_mem_erase (by rwa [← remove_active])
    exact (Nat.add_le_add_right (Finset.card_le_card (hsub x)) _).trans (hE.1.2.2.2 x hx')
  · intro x hx
    have hxy : x ≠ y := by rintro rfl; exact hS hx
    simpa [removeSite, hxy] using hE.2 x hx

/-- Deleting the sole live-site defect restores the ordinary domain rules. -/
theorem invariant_remove_consistent {G : Finset Plane} {E : Network G} {y arrival : Plane}
    (h : PrefixInvariant E y arrival) (hE : E.Auxiliary)
    (hS : y ∉ protectedSites G) : (removeSite E y).Consistent := by
  classical
  have haux := remove_auxiliary E y hE hS
  have hstat (x : Plane) (hx : x ≠ y) : (removeSite E y).status x = E.status x := by
    simp [removeSite, hx]
  refine ⟨⟨haux.1, ?_⟩, ?_, ?_, ?_⟩
  · intro x hx
    have hxy : x ≠ y := by rintro rfl; exact hS hx
    exact ⟨haux.2 x hx, h.u_full x (Finset.mem_filter.mp hx).1 hxy (hE.2 x hx)⟩
  · intro x hx hu
    have hxy : x ≠ y := by rintro rfl; simp [removeSite] at hu
    exact h.u_full x hx hxy ((hstat x hxy) ▸ hu)
  · intro x hx hd
    have hxy : x ≠ y := by rintro rfl; simp [removeSite] at hd
    exact h.d_two x hx hxy ((hstat x hxy) ▸ hd)
  · intro x hx z hz hadj
    rw [remove_active] at hx hz
    exact h.agree x (Finset.mem_of_mem_erase hx) z (Finset.mem_of_mem_erase hz) hadj

theorem invariant_nonarrival_present {G : Finset Plane} {E : Network G} {y arrival z : Plane}
    (h : PrefixInvariant E y arrival) (hy : y ∈ E.active) (hU : E.status y = .U)
    (hz : z ∈ (neighbors y).erase arrival ∩ E.active) : E.Present y z := by
  have hzn := (Finset.mem_erase.mp (Finset.mem_inter.mp hz).1).2
  have hza := (Finset.mem_erase.mp (Finset.mem_inter.mp hz).1).1
  have hzact := (Finset.mem_inter.mp hz).2
  have hzk : z ∈ E.kept y := by
    rw [h.liveU hU]
    exact Finset.mem_erase.mpr ⟨hza, Finset.mem_inter.mpr ⟨hzn, (Finset.mem_filter.mp hzact).1⟩⟩
  have hadj := (adjacent_iff y z).mpr hzn
  exact ⟨hy, hzact, hadj, hzk, (h.agree y hy z hzact hadj).mp hzk⟩

theorem neighbors_pair_distance {y a b : Plane} (ha : a ∈ neighbors y)
    (hb : b ∈ neighbors y) (hab : a ≠ b) : latticeDist a b = 2 := by
  obtain ⟨da, _, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨db, _, rfl⟩ := Finset.mem_image.mp hb
  have hd : da ≠ db := by rintro rfl; exact hab rfl
  cases da <;> cases db <;> simp_all [latticeDist, Compass.step]

theorem pair_type_pair {a b : Plane} (hd : latticeDist a b = 2) :
    HasPairType (responsePairType {a, b}) a b := by
  classical
  have hc : (∀ x ∈ ({a, b} : Finset Plane), ∀ y ∈ ({a, b} : Finset Plane),
      x.1 = y.1 ∨ x.2 = y.2) ↔ a.1 = b.1 ∨ a.2 = b.2 := by
    simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
    tauto
  unfold responsePairType HasPairType
  simp only [hc]
  by_cases he : a.1 = b.1 ∨ a.2 = b.2
  · simp [he, hd]
  · simp only [he, ite_false, reduceCtorEq]
    exact ⟨hd, not_or.mp he⟩

/-- Only non-arrival neighbors enter this closure assertion. -/
theorem invariant_pair_closure {G : Finset Plane} {E : Network G} {y arrival a b : Plane}
    (h : PrefixInvariant E y arrival) (hE : E.Auxiliary) (hy : y ∈ E.active)
    (hS : y ∉ protectedSites G) (hU : E.status y = .U)
    (ha : a ∈ (neighbors y).erase arrival ∩ E.active)
    (hb : b ∈ (neighbors y).erase arrival ∩ E.active) (hab : a ≠ b) :
    (removeSite E y).ResponsePair (responsePairType {a, b}) a b y := by
  have hpa := invariant_nonarrival_present h hy hU ha
  have hpb := invariant_nonarrival_present h hy hU hb
  have hay : a ≠ y := (adjacent_ne hpa.2.2.1).symm
  have hby : b ≠ y := (adjacent_ne hpb.2.2.1).symm
  have hneighbor (z : Plane) (hp : E.Present y z) (hzy : z ≠ y) :
      (removeSite E y).status z = .U ∨
        ((removeSite E y).status z = .D ∧ ((removeSite E y).presentNeighbors z).card ≤ 1) := by
    have hzG := (Finset.mem_filter.mp hp.2.1).1
    have hs := (Finset.mem_filter.mp hp.2.1).2
    have hstat : (removeSite E y).status z = E.status z := by simp [removeSite, hzy]
    cases hsz : E.status z with
    | U => exact Or.inl (hstat.trans hsz)
    | X => exact False.elim (hs hsz)
    | D =>
      right
      refine ⟨hstat.trans hsz, ?_⟩
      have hsub : (removeSite E y).presentNeighbors z ⊆ (E.kept z).erase y := by
        intro x hx
        have hx' := (remove_present E y z x).mp (Finset.mem_filter.mp hx).2
        exact Finset.mem_erase.mpr ⟨hx'.2.2, hx'.1.2.2.2.1⟩
      exact (Finset.card_le_card hsub).trans (by
        rw [Finset.card_erase_of_mem hp.2.2.2.2, h.d_two z hzG hzy hsz])
  refine ⟨invariant_remove_consistent h hE hS, ?_, ?_,
    (Finset.mem_filter.mp hy).1, by simp [removeSite], adjacent_symm hpa.2.2.1,
    adjacent_symm hpb.2.2.1, pair_type_pair ?_, hneighbor a hpa hay, hneighbor b hpb hby⟩
  · rw [remove_active]; exact Finset.mem_erase.mpr ⟨hay, hpa.2.1⟩
  · rw [remove_active]; exact Finset.mem_erase.mpr ⟨hby, hpb.2.1⟩
  · exact neighbors_pair_distance (Finset.mem_of_mem_erase (Finset.mem_inter.mp ha).1)
      (Finset.mem_of_mem_erase (Finset.mem_inter.mp hb).1) hab

def prefixDeparture (p : PairSetup) {n : ℕ} (T : Finset Plane) (w : DirectionWord n)
    (hw : StoppedNetworkTrail p.normalized p.u T w) (i : Fin n) : Departure := by
  classical
  let E := prefixNetwork p.normalized p.u w i.val
  let y := wordVertex p.u w i.val
  have hinv := (prefix_invariant p T w hw i.val (Nat.le_of_lt i.isLt)).1
  have hp := (prefix_invariant p T w hw i.val (Nat.le_of_lt i.isLt)).2 i le_rfl
  have hactive := hp.1
  have hs := (Finset.mem_filter.mp hactive).2
  have hstart : E.AdmissibleStart y := by
    refine ⟨hactive, (hw.2.2.1 i.val i.isLt).2, ?_⟩
    cases hsy : E.status y with
    | X => exact False.elim (hs hsy)
    | U =>
      left
      refine ⟨rfl, ?_⟩
      have hsub : E.presentNeighbors y ⊆ (neighbors y).erase (arrivalSite p w i.val) := by
        intro z hz
        have hk := (Finset.mem_filter.mp hz).2.2.2.2.1
        rw [hinv.liveU hsy] at hk
        exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hk).1,
          (Finset.mem_filter.mp hz).1⟩
      exact (Finset.card_le_card hsub).trans (by
        rw [Finset.card_erase_of_mem ((adjacent_iff _ _).mp hinv.arrival_adj), neighbors_card])
    | D =>
      right
      refine ⟨rfl, Finset.card_le_one.mpr ?_⟩
      intro x hx z hz
      exact hinv.liveD hsy x z (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hz).2
  exact ⟨p.G, p.τ, E, y, wordVertex p.u w (i.val + 1),
    (AKLT.W.REC050.main p T n w hw i.val (Nat.le_of_lt i.isLt)).1,
    hstart, present_mem_neighbors hp⟩

/-- The repaired, non-arrival-only response-pair leaf follows from the proved
strong prefix invariant. -/
theorem pair_closure : PairClosureStatementV2 := by
  intro p T n w hw i
  dsimp only
  intro hU a ha b hb hab
  have hi := (prefix_invariant p T w hw i.val (Nat.le_of_lt i.isLt)).1
  let hd := prefixDeparture p T w hw i
  apply invariant_pair_closure hi hd.auxiliary hd.start.1 hd.start.2.1 hU
  · simpa only [nonarrivalNeighborsV2, ← arrival_eq] using ha
  · simpa only [nonarrivalNeighborsV2, ← arrival_eq] using hb
  · exact hab

end AKLT.W.REC079
