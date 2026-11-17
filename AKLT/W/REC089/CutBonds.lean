import AKLT.W.REC089.CutGeometry

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC089

attribute [local instance] Classical.propDecidable

theorem inside_image_endpoints (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass)
    {e : Plane × Plane} (he : e ∈ (insideBonds a incoming).image (chartEdge a incoming)) :
    e.1 ∈ localSites a incoming ∧ e.2 ∈ localSites a incoming := by
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
  have hs := (AKLT.W.REC003.mem_internal _ _).mp (Finset.mem_filter.mp hf).1
  have h1 := (chart_mem_local a incoming f.1).mpr hs.1
  have h2 := (chart_mem_local a incoming f.2).mpr hs.2.2
  rcases chartEdge_cases a incoming f with h | h <;> simp_all

theorem crossing_image_endpoints (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass)
    {e : Plane × Plane}
    (he : e ∈ (crossingSlots a incoming).image (fun j => chartEdge a incoming (slotEdge j))) :
    (e.1 ∈ localSites a incoming ∧ e.2 ∉ localSites a incoming) ∨
      (e.2 ∈ localSites a incoming ∧ e.1 ∉ localSites a incoming) := by
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp he
  have h1 := (chart_mem_local a incoming (slotEdge j).1).mpr (slotEdge_facts j).1
  have h2 : localChart a incoming (slotEdge j).2 ∉ localSites a incoming := by
    rw [chart_mem_local]; exact (slotEdge_facts j).2.1
  rcases chartEdge_cases a incoming (slotEdge j) with h | h <;> simp_all

theorem cut_disjoint_oi (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass) :
    Disjoint (outsideBonds a incoming) ((insideBonds a incoming).image (chartEdge a incoming)) := by
  apply Finset.disjoint_left.mpr
  intro e ho hi
  exact (Finset.mem_filter.mp ho).2.1 (inside_image_endpoints a incoming hi).1

theorem cut_disjoint_c (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass) :
    Disjoint (outsideBonds a incoming ∪ (insideBonds a incoming).image (chartEdge a incoming))
      ((crossingSlots a incoming).image (fun j => chartEdge a incoming (slotEdge j))) := by
  apply Finset.disjoint_left.mpr
  intro e he hc
  rcases crossing_image_endpoints a incoming hc with hc | hc
  · rcases Finset.mem_union.mp he with he | he
    · exact (Finset.mem_filter.mp he).2.1 hc.1
    · exact hc.2 (inside_image_endpoints a incoming he).2
  · rcases Finset.mem_union.mp he with he | he
    · exact (Finset.mem_filter.mp he).2.2 hc.1
    · exact hc.2 (inside_image_endpoints a incoming he).1

theorem bond_product_cut (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass)
    (F : (Plane × Plane) → ℝ) :
    (∏ e ∈ a.D.bonds, F e) =
      (∏ e ∈ outsideBonds a incoming, F e) *
      (∏ e ∈ insideBonds a incoming, F (chartEdge a incoming e)) *
      ∏ j ∈ crossingSlots a incoming, F (chartEdge a incoming (slotEdge j)) := by
  conv_lhs => rw [bonds_cut_union a incoming,
    Finset.prod_union (cut_disjoint_c a incoming),
    Finset.prod_union (cut_disjoint_oi a incoming)]
  have hi : Set.InjOn (chartEdge a incoming) (↑(insideBonds a incoming) : Set (Plane × Plane)) :=
    fun e he f hf h => chartEdge_injective_internal a incoming
      (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp hf).1 h
  rw [Finset.prod_image hi,
    Finset.prod_image (fun _ _ _ _ h => chartEdge_injective_slots a incoming h)]

theorem pair_finset_eq (x z y o : Plane) :
    ({x, z} : Finset Plane) = {y, o} ↔ (x = y ∧ z = o) ∨ (x = o ∧ z = y) := by
  rw [← Finset.coe_inj]
  simpa using (Set.pair_eq_pair_iff (x := x) (y := z) (z := y) (w := o))

theorem trace_present_iff (a : AKLT.Blueprint.Rec.Departure) (hU : a.D.status a.y = .U)
    (x z : Plane) :
    (traceStep a.D a.y a.o).Present x z ↔ a.D.Present x z ∧
      ({x, z} : Finset Plane) ≠ {a.y, a.o} := by
  unfold Network.Present
  rw [trace_active a.D a.y a.o hU,
    AKLT.W.REC096.step_kept_iff, AKLT.W.REC096.step_kept_iff]
  simp only [ne_eq, pair_finset_eq]
  tauto

theorem trace_bonds_filter (a : AKLT.Blueprint.Rec.Departure) (hU : a.D.status a.y = .U) :
    (traceStep a.D a.y a.o).bonds =
      a.D.bonds.filter fun e => ({e.1, e.2} : Finset Plane) ≠ {a.y, a.o} := by
  ext e
  simp only [Network.bonds, Finset.mem_filter, trace_present_iff a hU]
  tauto

def networkBondTerm (a : AKLT.Blueprint.Rec.Departure) (next : Bool)
    (v : Plane → Vec3) (e : Plane × Plane) : ℝ :=
  if next ∧ ({e.1, e.2} : Finset Plane) = {a.y, a.o} then 1
  else 1 + dot (v e.1) (v e.2)

theorem trace_bond_product (a : AKLT.Blueprint.Rec.Departure) (hU : a.D.status a.y = .U)
    (next : Bool) (v : Plane → Vec3) :
    (∏ e ∈ (if next then traceStep a.D a.y a.o else a.D).bonds,
      (1 + dot (v e.1) (v e.2))) = ∏ e ∈ a.D.bonds, networkBondTerm a next v e := by
  cases next
  · rfl
  · simp only [ite_true, trace_bonds_filter a hU, Finset.prod_filter, networkBondTerm,
      true_and]
    apply Finset.prod_congr rfl
    intro e _
    split_ifs <;> simp_all

theorem networkBondTerm_chart (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass)
    (next : Bool) (v : Plane → Vec3) (e : Plane × Plane) :
    networkBondTerm a next v (chartEdge a incoming e) =
      networkBondTerm a next v (localChart a incoming e.1, localChart a incoming e.2) := by
  rcases chartEdge_cases a incoming e with h | h
  · rw [h]
  · simp only [h, networkBondTerm, Finset.pair_comm (localChart a incoming e.2),
      dot_comm (v (localChart a incoming e.2))]

theorem outgoing_local (a : AKLT.Blueprint.Rec.Departure) (incoming outgoing : Compass)
    (ho : a.o = a.y + outgoing.step) (π : PatternData) (hm : Matches a incoming outgoing π) :
    localChart a incoming π.outgoing.step = a.o := by
  change a.y + normalizeRotation incoming π.outgoing.step = a.o
  rw [hm.2.1, ho]

theorem network_drop_local (a : AKLT.Blueprint.Rec.Departure) (incoming outgoing : Compass)
    (ho : a.o = a.y + outgoing.step) (π : PatternData) (hm : Matches a incoming outgoing π)
    (z t : Plane) :
    ({localChart a incoming z, localChart a incoming t} : Finset Plane) = {a.y, a.o} ↔
      ({z, t} : Finset Plane) = {(0, 0), π.outgoing.step} := by
  have h0 : localChart a incoming (0, 0) = a.y := AKLT.W.REC096.chart_zero _ _
  have hout := outgoing_local a incoming outgoing ho π hm
  rw [← h0, ← hout]
  rw [pair_finset_eq, pair_finset_eq]
  have hi : Function.Injective (localChart a incoming) := (chartEquiv a incoming).injective
  constructor
  · rintro (⟨hz, ht⟩ | ⟨hz, ht⟩)
    · exact Or.inl ⟨hi hz, hi ht⟩
    · exact Or.inr ⟨hi hz, hi ht⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩

#print axioms bond_product_cut
#print axioms trace_bonds_filter

end AKLT.W.REC089
