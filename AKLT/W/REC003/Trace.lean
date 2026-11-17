module
public import AKLT.W.REC003.Integration

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC003

theorem trace_active {G : Finset Plane} (D : Network G) (y o : Plane)
    (hy : D.status y = .U) : (traceStep D y o).active = D.active := by
  ext x
  unfold Network.active
  simp only [Finset.mem_filter, traceStep, Function.update_apply]
  by_cases hx : x = y
  · subst x
    simp [hy]
  · simp [hx]

theorem trace_present_at_y {G : Finset Plane} (D : Network G) (y o z : Plane)
    (hy : D.status y = .U) (hyo : y ≠ o) :
    (traceStep D y o).Present y z ↔ D.Present y z ∧ z ≠ o := by
  unfold Network.Present
  rw [trace_active D y o hy]
  by_cases hzy : z = y
  · subst z
    simp [traceStep, hyo]
  · by_cases hzo : z = o
    · subst z
      simp [traceStep, hyo.symm]
    · simp [traceStep, hzy, hzo]

theorem trace_neighbors {G : Finset Plane} (D : Network G) (y o : Plane)
    (hy : D.status y = .U) (hyo : y ≠ o) :
    (traceStep D y o).presentNeighbors y = (D.presentNeighbors y).erase o := by
  ext z
  rw [mem_presentNeighbors, Finset.mem_erase, mem_presentNeighbors,
    trace_present_at_y D y o z hy hyo]
  tauto

theorem trace_present_off {G : Finset Plane} (D : Network G) (y o x z : Plane)
    (hy : D.status y = .U) (hx : x ≠ y) (hz : z ≠ y) :
    (traceStep D y o).Present x z ↔ D.Present x z := by
  unfold Network.Present
  rw [trace_active D y o hy]
  by_cases hxo : x = o <;> by_cases hzo : z = o <;>
    simp_all [traceStep]

theorem remove_trace_bonds {G : Finset Plane} (D : Network G) (y o : Plane)
    (hy : D.status y = .U) :
    (removeSite (traceStep D y o) y).bonds = (removeSite D y).bonds := by
  ext e
  constructor
  · intro he
    obtain ⟨hb, h₁, h₂⟩ := (mem_remove_bonds (traceStep D y o) y e).mp he
    have hp := Finset.mem_filter.mp hb
    apply (mem_remove_bonds D y e).mpr
    exact ⟨Finset.mem_filter.mpr ⟨hp.1,
      (trace_present_off D y o e.1 e.2 hy h₁ h₂).mp hp.2⟩, h₁, h₂⟩
  · intro he
    obtain ⟨hb, h₁, h₂⟩ := (mem_remove_bonds D y e).mp he
    have hp := Finset.mem_filter.mp hb
    apply (mem_remove_bonds (traceStep D y o) y e).mpr
    exact ⟨Finset.mem_filter.mpr ⟨hp.1,
      (trace_present_off D y o e.1 e.2 hy h₁ h₂).mpr hp.2⟩, h₁, h₂⟩

theorem partition_congr {G : Finset Plane} (D E : Network G)
    (hs : D.status = E.status) (hb : D.bonds = E.bonds) (τ : PinAssignment G)
    (b : Bool) (f : (Plane → Vec3) → ℝ) : D.partition τ b f = E.partition τ b f := by
  cases D with
  | mk sd kd =>
    cases E with
    | mk se ke =>
      change sd = se at hs
      subst se
      unfold Network.partition
      dsimp only [Network.active, Network.spins]
      rw [hb]
      rfl

theorem remove_trace_partition {G : Finset Plane} (D : Network G) (y o : Plane)
    (hy : D.status y = .U) (τ : PinAssignment G) (b : Bool)
    (f : (Plane → Vec3) → ℝ) :
    (removeSite (traceStep D y o) y).partition τ b f =
      (removeSite D y).partition τ b f := by
  apply partition_congr _ _ _ (remove_trace_bonds D y o hy)
  funext x
  simp [removeSite, traceStep, Function.update_apply]

end AKLT.W.REC003
