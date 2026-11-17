import AKLT.W.REC022.Integrate

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC022

variable {G : Finset Plane}

theorem active_trace (D : Network G) (y o : Plane) (hU : D.status y = .U) :
    (traceStep D y o).active = D.active := by
  ext x
  rw [Network.active,Finset.mem_filter,Network.active,Finset.mem_filter]
  change (x ∈ G ∧ Function.update D.status y
    (if D.status y = .U then .D else .X) x ≠ .X) ↔
    (x ∈ G ∧ D.status x ≠ .X)
  rw [hU]
  by_cases hx : x = y
  · subst x; simp [hU]
  · simp [hx]

theorem trace_neighbours (D : Network G) (y o : Plane) (hU : D.status y = .U)
    (hyo : y ≠ o) :
    (traceStep D y o).presentNeighbours y = (D.presentNeighbours y).erase o := by
  ext z
  rw [mem_presentNeighbours,Finset.mem_erase,mem_presentNeighbours]
  simp only [Network.Present,active_trace D y o hU]
  simp only [traceStep,ite_true]
  by_cases hzy : z = y
  · subst z; simp [Adjacent,latticeDist]
  · by_cases hzo : z = o
    · subst z; simp [Ne.symm hyo]
    · simp [hzy,hzo,Finset.mem_erase]

theorem remove_trace_status (D : Network G) (y o : Plane) :
    (removeSite (traceStep D y o) y).status = (removeSite D y).status := by
  funext x
  by_cases hx : x = y
  · subst x; simp [removeSite]
  · simp [removeSite,traceStep,hx]

theorem remove_trace_bonds (D : Network G) (y o : Plane) :
    (removeSite (traceStep D y o) y).bonds = (removeSite D y).bonds := by
  have ha : (removeSite (traceStep D y o) y).active = (removeSite D y).active := by
    unfold Network.active
    rw [remove_trace_status]
  ext e
  rw [Network.bonds,Finset.mem_filter,Network.bonds,Finset.mem_filter]
  simp only [Network.Present,ha]
  by_cases hx : e.1 = y
  · have hn : e.1 ∉ (removeSite D y).active := by rw [active_remove]; simp [hx]
    simp [hn]
  · by_cases hz : e.2 = y
    · have hn : e.2 ∉ (removeSite D y).active := by rw [active_remove]; simp [hz]
      simp [hn]
    · by_cases hxo : e.1 = o <;> by_cases hzo : e.2 = o <;>
        simp_all [removeSite,traceStep,Finset.mem_erase]

theorem partition_congr (D E : Network G)
    (hs : D.status = E.status) (hb : D.bonds = E.bonds)
    (τ : PinAssignment G) (b : Bool) (f : (Plane → Vec3) → ℝ) :
    D.partition τ b f = E.partition τ b f := by
  rcases D with ⟨s,k⟩
  rcases E with ⟨s',k'⟩
  dsimp only at hs
  subst s'
  unfold Network.partition
  rw [hb]
  rfl

theorem remove_trace_partition (D : Network G) (y o : Plane)
    (τ : PinAssignment G) (b : Bool) (f : (Plane → Vec3) → ℝ) :
    (removeSite (traceStep D y o) y).partition τ b f =
      (removeSite D y).partition τ b f :=
  partition_congr _ _ (remove_trace_status D y o) (remove_trace_bonds D y o) τ b f

end AKLT.W.REC022
