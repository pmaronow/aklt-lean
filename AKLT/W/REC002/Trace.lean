module
public import AKLT.W.REC002.Integration

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC002

theorem trace_active {G : Finset Plane} (D : Network G) (y o : Plane)
    (hU : D.status y = .U) : (traceStep D y o).active = D.active := by
  ext x
  by_cases h : x = y <;>
    simp [Network.active, traceStep, Function.update_apply, h, hU]

theorem trace_present_y {G : Finset Plane} (D : Network G) (y o z : Plane)
    (hU : D.status y = .U) (_hyo : y ≠ o) :
    (traceStep D y o).Present y z ↔ D.Present y z ∧ z ≠ o := by
  simp only [Network.Present, trace_active D y o hU]
  by_cases hzy : z = y
  · subst z
    simp [Adjacent, latticeDist]
  · by_cases hzo : z = o
    · subst z
      simp [traceStep]
    · simp [traceStep, hzy, hzo]

theorem trace_neighbors {G : Finset Plane} (D : Network G) (y o : Plane)
    (hU : D.status y = .U) (hyo : y ≠ o) :
    (traceStep D y o).presentNeighbors y = (D.presentNeighbors y).erase o := by
  ext z
  simp only [mem_presentNeighbors, trace_present_y D y o z hU hyo,
    Finset.mem_erase]
  tauto

theorem trace_kept_away {G : Finset Plane} (D : Network G) (y o x z : Plane)
    (hx : x ≠ y) (hz : z ≠ y) :
    z ∈ (traceStep D y o).kept x ↔ z ∈ D.kept x := by
  dsimp only [traceStep]
  rw [ite_eq_right hx]
  split_ifs <;> simp [hz]

theorem trace_present_away {G : Finset Plane} (D : Network G) (y o x z : Plane)
    (hU : D.status y = .U) (hx : x ≠ y) (hz : z ≠ y) :
    (traceStep D y o).Present x z ↔ D.Present x z := by
  simp only [Network.Present, trace_active D y o hU,
    trace_kept_away D y o x z hx hz, trace_kept_away D y o z x hz hx]

theorem remove_trace_status {G : Finset Plane} (D : Network G) (y o : Plane) :
    (removeSite (traceStep D y o) y).status = (removeSite D y).status := by
  funext x
  by_cases h : x = y <;> simp [removeSite, traceStep, h]

theorem remove_trace_bonds {G : Finset Plane} (D : Network G) (y o : Plane)
    (hU : D.status y = .U) :
    (removeSite (traceStep D y o) y).bonds = (removeSite D y).bonds := by
  rw [remove_bonds, remove_bonds]
  ext ⟨x, z⟩
  simp only [Finset.mem_filter, mem_bonds]
  by_cases hx : x = y <;> by_cases hz : z = y
  · simp [hx]
  · simp [hx]
  · simp [hz]
  · simp [hx, hz, trace_present_away D y o x z hU hx hz]

theorem partition_congr {G : Finset Plane} (D E : Network G)
    (hstatus : D.status = E.status) (hbonds : D.bonds = E.bonds)
    (τ : PinAssignment G) (b : Bool) (f : (Plane → Vec3) → ℝ) :
    D.partition τ b f = E.partition τ b f := by
  have hactive : D.active = E.active := by simp only [Network.active, hstatus]
  rw [partition_spinSum, partition_spinSum, hactive, hstatus, hbonds]

theorem remove_trace_partition {G : Finset Plane} (D : Network G) (y o : Plane)
    (hU : D.status y = .U) (τ : PinAssignment G) (b : Bool)
    (f : (Plane → Vec3) → ℝ) :
    (removeSite (traceStep D y o) y).partition τ b f =
      (removeSite D y).partition τ b f :=
  partition_congr _ _ (remove_trace_status D y o) (remove_trace_bonds D y o hU) τ b f

end AKLT.W.REC002
