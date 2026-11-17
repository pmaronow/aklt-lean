module
public import AKLT.W.REC096.Geometry

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC096

theorem present_symm {G : Finset Plane} {E : Network G} {x z : Plane}
    (h : E.Present x z) : E.Present z x :=
  ⟨h.2.1, h.1, adjacent_symm h.2.2.1, h.2.2.2.2, h.2.2.2.1⟩

theorem present_mem_neighbors {G : Finset Plane} {E : Network G} {x z : Plane}
    (h : E.Present x z) : z ∈ E.presentNeighbors x := by
  exact Finset.mem_filter.mpr ⟨(adjacent_iff _ _).mp h.2.2.1, h⟩

theorem step_status_ne {G : Finset Plane} (E : Network G) (y o x : Plane)
    (hx : x ≠ y) : (traceStep E y o).status x = E.status x := by
  simp [traceStep, hx]

theorem step_active_subset {G : Finset Plane} (E : Network G) (y o : Plane) :
    (traceStep E y o).active ⊆ E.active := by
  intro x hx
  simp only [Network.active, Finset.mem_filter] at hx ⊢
  refine ⟨hx.1, ?_⟩
  by_cases hxy : x = y
  · subst x
    by_cases hU : E.status y = .U
    · simp [hU]
    · simp [traceStep, hU] at hx
  · simpa [step_status_ne E y o x hxy] using hx.2

theorem step_kept_iff {G : Finset Plane} (E : Network G) (y o x z : Plane) :
    z ∈ (traceStep E y o).kept x ↔
      z ∈ E.kept x ∧ ¬(x = y ∧ z = o) ∧ ¬(x = o ∧ z = y) := by
  by_cases hxy : x = y <;> by_cases hxo : x = o <;>
    simp_all [traceStep] <;> tauto

/-- The sole exceptional kept set is at the live endpoint. -/
structure PrefixInvariant {G : Finset Plane} (E : Network G) (y a : Plane) : Prop where
  outside : ∀ x, x ∉ G → E.status x = .X
  kept_sub : ∀ x, E.kept x ⊆ neighbors x ∩ G
  u_full : ∀ x ∈ G, x ≠ y → E.status x = .U → E.kept x = neighbors x ∩ G
  d_two : ∀ x ∈ G, x ≠ y → E.status x = .D → (E.kept x).card = 2
  agree : ∀ x ∈ E.active, ∀ z ∈ E.active, Adjacent x z →
    (z ∈ E.kept x ↔ x ∈ E.kept z)
  arrival_adj : Adjacent y a
  arrival_notU : E.status a ≠ .U
  liveU : E.status y = .U → E.kept y = (neighbors y ∩ G).erase a
  liveD : E.status y = .D → ∀ x z, E.Present y x → E.Present y z → x = z

theorem invariant_step {G : Finset Plane} {E : Network G} {y a o : Plane}
    (h : PrefixInvariant E y a) (hS : y ∉ protectedSites G)
    (hp : E.Present y o) : PrefixInvariant (traceStep E y o) o y := by
  classical
  have hyG := (Finset.mem_filter.mp hp.1).1
  have hoG := (Finset.mem_filter.mp hp.2.1).1
  have hyo := adjacent_ne hp.2.2.1
  have hfull : neighbors y ∩ G = neighbors y := by
    apply Finset.inter_eq_left.mpr
    intro z hz
    exact interior_ball hyG hS (by rw [← adjacent_iff] at hz; exact hz.le.trans (by decide))
  have hUcard (hu : E.status y = .U) : (E.kept y).card = 3 := by
    rw [h.liveU hu, hfull, Finset.card_erase_of_mem ((adjacent_iff _ _).mp h.arrival_adj),
      neighbors_card]
  refine ⟨?_, ?_, ?_, ?_, ?_, adjacent_symm hp.2.2.1, ?_, ?_, ?_⟩
  · intro x hx
    rw [step_status_ne E y o x (fun he => hx (he ▸ hyG))]
    exact h.outside x hx
  · intro x z hz
    exact h.kept_sub x ((step_kept_iff E y o x z).mp hz).1
  · intro x hx hxo hu
    have hxy : x ≠ y := by
      rintro rfl
      simp only [traceStep, Function.update_self] at hu
      split_ifs at hu
    rw [step_status_ne E y o x hxy] at hu
    simpa [traceStep, hxy, hxo] using h.u_full x hx hxy hu
  · intro x hx hxo hd
    by_cases hxy : x = y
    · subst x
      have hu : E.status y = .U := by
        by_contra hn
        simp [traceStep, hn] at hd
      simp [traceStep, Finset.card_erase_of_mem hp.2.2.2.1, hUcard hu]
    · rw [step_status_ne E y o x hxy] at hd
      simpa [traceStep, hxy, hxo] using h.d_two x hx hxy hd
  · intro x hx z hz hadj
    have hm := h.agree x (step_active_subset E y o hx)
      z (step_active_subset E y o hz) hadj
    rw [step_kept_iff, step_kept_iff]
    tauto
  · simp [traceStep]
    split_ifs <;> simp
  · intro hu
    have hou : E.status o = .U := by simpa [step_status_ne E y o o hyo.symm] using hu
    simpa [traceStep, hyo.symm] using
      congrArg (fun k : Finset Plane => k.erase y) (h.u_full o hoG hyo.symm hou)
  · intro hd x z hpx hpz
    have hod : E.status o = .D := by simpa [step_status_ne E y o o hyo.symm] using hd
    have hc : ((traceStep E y o).kept o).card = 1 := by
      simp [traceStep, hyo.symm, Finset.card_erase_of_mem hp.2.2.2.2,
        h.d_two o hoG hyo.symm hod]
    exact (Finset.card_le_one.mp (Nat.le_of_eq hc)) x hpx.2.2.2.1 z hpz.2.2.2.1

theorem step_preserves_unused {G : Finset Plane} {E : Network G} {y a o x z : Plane}
    (h : PrefixInvariant E y a) (hp : E.Present y o)
    (hxz : E.Present x z) (hne : ({x, z} : Finset Plane) ≠ {y, o}) :
    (traceStep E y o).Present x z := by
  classical
  have hn₁ : ¬(x = y ∧ z = o) := by rintro ⟨rfl, rfl⟩; exact hne rfl
  have hn₂ : ¬(x = o ∧ z = y) := by
    rintro ⟨rfl, rfl⟩
    exact hne (Finset.pair_comm _ _)
  have hactive (t b : Plane) (htb : E.Present t b)
      (hne : ({t, b} : Finset Plane) ≠ {y, o}) : t ∈ (traceStep E y o).active := by
    have htG := (Finset.mem_filter.mp htb.1).1
    by_cases hty : t = y
    · subst t
      have hu : E.status y = .U := by
        have hnx := (Finset.mem_filter.mp hp.1).2
        by_contra hn
        have hd : E.status y = .D := by cases hs : E.status y <;> simp_all
        have hbo := h.liveD hd b o htb hp
        exact hne (by rw [hbo])
      simp [Network.active, traceStep, htG, hu]
    · simpa [Network.active, step_status_ne E y o t hty] using htb.1
  exact ⟨hactive x z hxz hne,
    hactive z x (present_symm hxz) (by simpa only [Finset.pair_comm z x] using hne),
    hxz.2.2.1, (step_kept_iff _ _ _ _ _).mpr ⟨hxz.2.2.2.1, hn₁, hn₂⟩,
    (step_kept_iff _ _ _ _ _).mpr ⟨hxz.2.2.2.2, by tauto, by tauto⟩⟩

end AKLT.W.REC096
