module
public import AKLT.W.REC017.Geometry

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC017

theorem remove_active {G : Finset Plane} (D : Network G) (y : Plane) :
    (removeSite D y).active = D.active.erase y := by
  ext x
  by_cases hx : x = y <;> simp [Network.active, removeSite, Function.update_apply, hx]

theorem remove_present {G : Finset Plane} (D : Network G) (y x z : Plane) :
    (removeSite D y).Present x z ↔ D.Present x z ∧ x ≠ y ∧ z ≠ y := by
  simp only [Network.Present, remove_active, Finset.mem_erase]
  dsimp only [removeSite]
  tauto

theorem remove_bonds {G : Finset Plane} (D : Network G) (y : Plane) :
    (removeSite D y).bonds = D.bonds.filter (fun e => e.1 ≠ y ∧ e.2 ≠ y) := by
  ext e
  simp only [mem_bonds, Finset.mem_filter, remove_present]
  tauto

def bondProduct {G : Finset Plane} (D : Network G) (n : Plane → Vec3) : ℝ :=
  ∏ e ∈ D.bonds, (1 + dot (n e.1) (n e.2))

def otherEnd (y : Plane) (e : Plane × Plane) : Plane :=
  if e.1 = y then e.2 else e.1

theorem incident_other {G : Finset Plane} {D : Network G} {y : Plane}
    {e : Plane × Plane} (he : e ∈ D.bonds) (hi : e.1 = y ∨ e.2 = y) :
    otherEnd y e ∈ D.presentNeighbors y := by
  rcases mem_bonds.mp he with ⟨hp, he⟩
  rcases hi with h | h
  · simp only [otherEnd, h, ite_true]
    subst y
    exact Finset.mem_filter.mpr ⟨positive_neighbor hp, he⟩
  · have hn : e.1 ≠ y := by rw [← h]; exact positive_ne _ _ hp
    simp only [otherEnd, hn, ite_false]
    subst y
    exact Finset.mem_filter.mpr ⟨reverse_positive_neighbor hp, present_symm he⟩

theorem incident_injective {G : Finset Plane} {D : Network G} {y : Plane}
    {e f : Plane × Plane} (he : e ∈ D.bonds) (hf : f ∈ D.bonds)
    (hei : e.1 = y ∨ e.2 = y) (hfi : f.1 = y ∨ f.2 = y)
    (hv : otherEnd y e = otherEnd y f) : e = f := by
  have hep := (mem_bonds.mp he).1
  have hfp := (mem_bonds.mp hf).1
  by_cases h1 : e.1 = y <;> by_cases h2 : f.1 = y
  · simp only [otherEnd, h1, h2, ite_true] at hv
    exact Prod.ext (h1.trans h2.symm) hv
  · have h2' := hfi.resolve_left h2
    simp only [otherEnd, h1, h2, ite_true, ite_false] at hv
    exfalso
    apply positive_no_reverse e.1 e.2 hep
    simpa only [h1, h2', ← hv] using hfp
  · have h1' := hei.resolve_left h1
    simp only [otherEnd, h1, h2, ite_true, ite_false] at hv
    exfalso
    apply positive_no_reverse f.1 f.2 hfp
    simpa only [h2, h1', hv] using hep
  · have h1' := hei.resolve_left h1
    have h2' := hfi.resolve_left h2
    simp only [otherEnd, h1, h2, ite_false] at hv
    exact Prod.ext hv (h1'.trans h2'.symm)

theorem incident_surjective {G : Finset Plane} {D : Network G} {y z : Plane}
    (hz : z ∈ D.presentNeighbors y) :
    ∃ e ∈ D.bonds, (e.1 = y ∨ e.2 = y) ∧ otherEnd y e = z := by
  rcases Finset.mem_filter.mp hz with ⟨hn, hp⟩
  rcases neighbor_orientation hn with h | h
  · refine ⟨(y, z), mem_bonds.mpr ⟨h, hp⟩, Or.inl rfl, ?_⟩
    simp [otherEnd]
  · refine ⟨(z, y), mem_bonds.mpr ⟨h, present_symm hp⟩, Or.inr rfl, ?_⟩
    simp [otherEnd, positive_ne _ _ h]

theorem bondProduct_split {G : Finset Plane} (D : Network G) (y : Plane)
    (n : Plane → Vec3) (v : Vec3) :
    bondProduct D (Function.update n y v) =
      bondProduct (removeSite D y) n *
        ∏ z ∈ D.presentNeighbors y, (1 + dot v (n z)) := by
  classical
  let p := fun e : Plane × Plane => e.1 ≠ y ∧ e.2 ≠ y
  unfold bondProduct
  rw [← Finset.prod_filter_mul_prod_filter_not D.bonds p]
  have haway : (∏ e ∈ D.bonds.filter p,
      (1 + dot (Function.update n y v e.1) (Function.update n y v e.2))) =
      ∏ e ∈ (removeSite D y).bonds, (1 + dot (n e.1) (n e.2)) := by
    rw [remove_bonds]
    apply Finset.prod_congr rfl
    intro e he
    rcases Finset.mem_filter.mp he with ⟨_, hx, hz⟩
    rw [Function.update_of_ne hx, Function.update_of_ne hz]
  rw [haway]
  congr 1
  apply Finset.prod_bij (fun e _ => otherEnd y e)
  · intro e he
    rcases Finset.mem_filter.mp he with ⟨he, hi⟩
    exact incident_other he (by simpa only [p, not_and_or, not_not] using hi)
  · intro e he f hf hv
    rcases Finset.mem_filter.mp he with ⟨he, hi⟩
    rcases Finset.mem_filter.mp hf with ⟨hf, hj⟩
    exact incident_injective he hf
      (by simpa only [p, not_and_or, not_not] using hi)
      (by simpa only [p, not_and_or, not_not] using hj) hv
  · intro z hz
    rcases incident_surjective hz with ⟨e, he, hi, hv⟩
    refine ⟨e, Finset.mem_filter.mpr ⟨he, ?_⟩, hv⟩
    simpa only [p, not_and_or, not_not] using hi
  · intro e he
    rcases Finset.mem_filter.mp he with ⟨he, hi⟩
    have hp := (mem_bonds.mp he).1
    have hi : e.1 = y ∨ e.2 = y := by simpa only [p, not_and_or, not_not] using hi
    rcases hi with hx | hz
    · have hn : e.2 ≠ y := by rw [← hx]; exact (positive_ne _ _ hp).symm
      simp [otherEnd, hx, Function.update_of_ne hn]
    · have hn : e.1 ≠ y := by rw [← hz]; exact positive_ne _ _ hp
      simp [otherEnd, hn, hz, dot_comm (n e.1) v]

theorem trace_active {G : Finset Plane} (D : Network G) (y o : Plane)
    (hy : D.status y = .U) : (traceStep D y o).active = D.active := by
  ext x
  by_cases hx : x = y <;> simp [Network.active, traceStep, hx, hy]

theorem trace_present {G : Finset Plane} (D : Network G) (y o x z : Plane)
    (hy : D.status y = .U) :
    (traceStep D y o).Present x z ↔ D.Present x z ∧
      ¬(x = y ∧ z = o ∨ x = o ∧ z = y) := by
  simp only [Network.Present, trace_active D y o hy]
  by_cases hxy : x = y <;> by_cases hxo : x = o <;>
    by_cases hzy : z = y <;> by_cases hzo : z = o <;>
    simp_all [traceStep]

theorem trace_neighbors {G : Finset Plane} (D : Network G) (y o : Plane)
    (hy : D.status y = .U) (hne : y ≠ o) :
    (traceStep D y o).presentNeighbors y = (D.presentNeighbors y).erase o := by
  ext z
  simp only [Network.presentNeighbors, Finset.mem_filter, Finset.mem_erase,
    trace_present D y o y z hy]
  simp only [true_and]
  tauto

end AKLT.W.REC017
