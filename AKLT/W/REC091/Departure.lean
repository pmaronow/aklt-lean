module
public import AKLT.W.REC091.OneSite
public import AKLT.Blueprint.Rec.NodesV2Local

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC091

theorem originalLeg_outside {G : Finset Plane} {e : Plane × Plane}
    (he : e ∈ originalLegs G) : e.2 ∉ G := by
  obtain ⟨x, _, hx⟩ := Finset.mem_biUnion.mp he
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
  exact (Finset.mem_sdiff.mp hz).2

theorem neighbour_distance {y z : Plane} (hz : z ∈ neighbours y) : latticeDist y z = 1 := by
  obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hz
  cases d <;> dsimp [latticeDist, Compass.step] <;> omega

theorem no_original_leg_of_unprotected {G : Finset Plane} {y : Plane}
    (hy : y ∈ G) (hs : y ∉ protectedSites G) :
    ∀ e : originalLegs G, e.val.1 ≠ y := by
  intro e he
  have hdist : latticeDist y e.val.2 = 1 := by
    rw [← he]
    exact neighbour_distance (originalLeg_neighbour e.property)
  have hdepth : boundaryDepth G y ≤ 1 := by
    have h : boundaryDepth G y ≤ (latticeDist y e.val.2 : ℕ∞) :=
      iInf_le (fun z : {z : Plane // z ∉ G} => (latticeDist y z.val : ℕ∞))
        ⟨e.val.2, originalLeg_outside e.property⟩
    simpa only [hdist, Nat.cast_one] using h
  apply hs
  change y ∈ G.filter (fun x => boundaryDepth G x ≤ 2)
  exact Finset.mem_filter.mpr ⟨hy, hdepth.trans (by norm_num)⟩

theorem trace_active {G : Finset Plane} (D : Network G) (y o : Plane) (hU : D.status y = .U) :
    (traceStep D y o).active = D.active := by
  classical
  ext x
  simp only [Network.active, Finset.mem_filter]
  by_cases hx : x = y
  · subst x
    simp [traceStep, hU]
  · simp [traceStep, hx]

theorem trace_neighbours {G : Finset Plane} (D : Network G) (y o : Plane)
    (hU : D.status y = .U) :
    (traceStep D y o).presentNeighbours y = (D.presentNeighbours y).erase o := by
  classical
  ext z
  rw [Network.presentNeighbours, Finset.mem_filter, Finset.mem_erase,
    Network.presentNeighbours, Finset.mem_filter]
  simp only [Network.Present, trace_active D y o hU]
  by_cases hz : z = y
  · subst z
    simp [Adjacent, latticeDist]
  · by_cases ho : z = o
    · subst z
      simp [traceStep, hz]
    · simp only [traceStep, ite_eq_left, hz, ho, Finset.mem_erase]
      tauto

theorem remove_trace_status {G : Finset Plane} (D : Network G) (y o : Plane) :
    (removeSite (traceStep D y o) y).status = (removeSite D y).status := by
  funext x
  by_cases hx : x = y <;> simp [removeSite, traceStep, hx]

theorem remove_trace_bonds {G : Finset Plane} (D : Network G) (y o : Plane) :
    (removeSite (traceStep D y o) y).bonds = (removeSite D y).bonds := by
  classical
  have ha : (removeSite (traceStep D y o) y).active = (removeSite D y).active := by
    unfold Network.active
    rw [remove_trace_status]
  ext e
  rw [Network.bonds, Finset.mem_filter, Network.bonds, Finset.mem_filter]
  simp only [Network.Present, ha]
  by_cases hx : e.1 = y
  · simp [mem_remove_active, hx]
  · by_cases hz : e.2 = y
    · simp [mem_remove_active, hz]
    · change (_ ∧ _ ∧ _ ∧ _ ∧ e.2 ∈ (traceStep D y o).kept e.1 ∧
        e.1 ∈ (traceStep D y o).kept e.2) ↔
        (_ ∧ _ ∧ _ ∧ _ ∧ e.2 ∈ D.kept e.1 ∧ e.1 ∈ D.kept e.2)
      simp only [traceStep, hx, hz]
      split_ifs <;> simp only [Finset.mem_erase] <;> tauto

theorem partition_congr {G : Finset Plane} {D E : Network G}
    (hs : D.status = E.status) (hb : D.bonds = E.bonds)
    (τ : PinAssignment G) (b : Bool) (f : (Plane → Vec3) → ℝ) :
    D.partition τ b f = E.partition τ b f := by
  unfold Network.partition Network.spins Network.active
  rw [hs, hb]

theorem remove_trace_partition {G : Finset Plane} (D : Network G) (y o : Plane)
    (τ : PinAssignment G) (b : Bool) (f : (Plane → Vec3) → ℝ) :
    (removeSite (traceStep D y o) y).partition τ b f = (removeSite D y).partition τ b f :=
  partition_congr (remove_trace_status D y o) (remove_trace_bonds D y o) τ b f

/-- The two finite disintegrations used in departure integration. -/
theorem departure_disintegration (a : Departure) (hU : a.D.status a.y = .U) (b : Bool) :
    a.D.partition a.τ b (fun _ => 1) =
      (removeSite a.D a.y).partition a.τ b (fun n => siteFunctional .U
        (fun v => ∏ z ∈ a.D.presentNeighbours a.y, (1 + dot v (n z)))) ∧
    (traceStep a.D a.y a.o).partition a.τ b (fun _ => 1) =
      (removeSite a.D a.y).partition a.τ b (fun n => siteFunctional .D
        (fun v => ∏ z ∈ (a.D.presentNeighbours a.y).erase a.o, (1 + dot v (n z)))) := by
  have hy := a.start.1
  have hleg := no_original_leg_of_unprotected (Finset.mem_filter.mp hy).1 a.start.2.1
  constructor
  · simpa only [hU] using partition_integrate_site a.D a.τ b a.y hy hleg
  · have hy' : a.y ∈ (traceStep a.D a.y a.o).active := by rw [trace_active _ _ _ hU]; exact hy
    have h := partition_integrate_site (traceStep a.D a.y a.o) a.τ b a.y hy' hleg
    have hs : (traceStep a.D a.y a.o).status a.y = .D := by simp [traceStep, hU]
    simpa only [hs, trace_neighbours _ _ _ hU, remove_trace_partition] using h

end AKLT.W.REC091
