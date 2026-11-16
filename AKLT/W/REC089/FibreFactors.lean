import AKLT.W.REC089.ExternalFields
import AKLT.W.REC089.InternalBonds

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC089

attribute [local instance] Classical.propDecidable

def exteriorFactor (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass)
    (ω : ExteriorSpins a incoming) : ℝ :=
  (∏ e ∈ outsideBonds a incoming,
    (1 + dot (exteriorSpin a incoming ω e.1) (exteriorSpin a incoming ω e.2))) *
    outsidePinProduct a incoming (exteriorSpin a incoming ω)

theorem exteriorFactor_nonneg (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass)
    (ω : ExteriorSpins a incoming) : 0 ≤ exteriorFactor a incoming ω := by
  apply mul_nonneg
  · exact Finset.prod_nonneg fun e _ => ball_factor_nonneg _ _
      (exteriorSpin_ball a incoming ω _) (exteriorSpin_ball a incoming ω _)
  · apply Finset.prod_nonneg
    intro e _
    unfold pinTerm
    split_ifs
    · exact ball_factor_nonneg _ _ (pinField_ball a e) (exteriorSpin_ball a incoming ω _)
    · norm_num

theorem slot_source_not_zero (j : Fin 20) : (slotEdge j).1 ≠ (0, 0) := by
  revert j
  decide +kernel

theorem crossing_term (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass)
    (next : Bool) (v : Plane → Vec3) (j : Fin 20) :
    networkBondTerm a next v (chartEdge a incoming (slotEdge j)) =
      1 + dot (v (physicalSlot a incoming j).1) (v (physicalSlot a incoming j).2) := by
  have h0 : localChart a incoming (0, 0) = a.y := AKLT.W.REC096.chart_zero _ _
  have h1 : (physicalSlot a incoming j).1 ≠ a.y := by
    rw [← h0]
    exact (chartEquiv a incoming).injective.ne (slot_source_not_zero j)
  have h2 : (physicalSlot a incoming j).2 ≠ a.y := by
    intro h
    exact (physicalSlot_facts a incoming j).2.1 (h ▸ centre_mem_localSites a incoming)
  have hn : ({(physicalSlot a incoming j).1, (physicalSlot a incoming j).2} : Finset Plane) ≠
      {a.y, a.o} := by
    simp only [ne_eq, pair_finset_eq]
    tauto
  rw [networkBondTerm_chart]
  change (if next ∧ ({(physicalSlot a incoming j).1, (physicalSlot a incoming j).2} : Finset Plane) =
    {a.y, a.o} then 1 else _) = _
  simp only [hn, and_false, ite_false]
  rfl

theorem outside_bond_product (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass)
    (ω : ExteriorSpins a incoming) (next : Bool) (v : Plane → Vec3)
    (hv : ∀ x, x ∉ localSites a incoming → v x = exteriorSpin a incoming ω x) :
    (∏ e ∈ outsideBonds a incoming, networkBondTerm a next v e) =
      ∏ e ∈ outsideBonds a incoming,
        (1 + dot (exteriorSpin a incoming ω e.1) (exteriorSpin a incoming ω e.2)) := by
  apply Finset.prod_congr rfl
  intro e he
  have h := (Finset.mem_filter.mp he).2
  have h1 : e.1 ≠ a.y := fun hy => h.1 (hy ▸ centre_mem_localSites a incoming)
  have h2 : e.2 ≠ a.y := fun hy => h.2 (hy ▸ centre_mem_localSites a incoming)
  have hn : ({e.1, e.2} : Finset Plane) ≠ {a.y, a.o} := by
    simp only [ne_eq, pair_finset_eq]
    tauto
  simp only [networkBondTerm, hn, and_false, ite_false, hv e.1 h.1, hv e.2 h.2]

theorem outside_pin_product (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass)
    (ω : ExteriorSpins a incoming) (v : Plane → Vec3)
    (hv : ∀ x, x ∉ localSites a incoming → v x = exteriorSpin a incoming ω x) :
    outsidePinProduct a incoming v = outsidePinProduct a incoming (exteriorSpin a incoming ω) := by
  apply Finset.prod_congr rfl
  intro e he
  unfold pinTerm
  rw [hv e.1 (Finset.mem_filter.mp he).2]

def localSlotProduct (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass)
    (b : Fin 20 → Vec3) (v : Plane → Vec3) : ℝ :=
  ∏ j : Fin 20, if a.D.status (physicalSlot a incoming j).1 = .X then 1
    else 1 + dot (b j) (v (physicalSlot a incoming j).1)

theorem network_factors_cut (a : AKLT.Blueprint.Rec.Departure) (hU : a.D.status a.y = .U)
    (incoming : Compass) (ω : ExteriorSpins a incoming) (next : Bool) (v : Plane → Vec3)
    (hv : ∀ x, x ∉ localSites a incoming → v x = exteriorSpin a incoming ω x) :
    ((∏ e ∈ (if next then traceStep a.D a.y a.o else a.D).bonds,
      (1 + dot (v e.1) (v e.2))) *
      ∏ e : originalLegs a.G, if e.val.1 ∈ a.D.active then
        1 + dot (a.τ e).val (v e.val.1) else 1) =
      exteriorFactor a incoming ω *
        (∏ e ∈ insideBonds a incoming, networkBondTerm a next v (chartEdge a incoming e)) *
          localSlotProduct a incoming (slotField a incoming ω) v := by
  rw [trace_bond_product a hU, bond_product_cut, pin_product_cut,
    outside_bond_product a incoming ω next v hv, outside_pin_product a incoming ω v hv]
  have hc : (∏ j ∈ crossingSlots a incoming,
      networkBondTerm a next v (chartEdge a incoming (slotEdge j))) =
      ∏ j : Fin 20, if a.D.Present (physicalSlot a incoming j).1 (physicalSlot a incoming j).2
        then 1 + dot (v (physicalSlot a incoming j).1) (v (physicalSlot a incoming j).2) else 1 := by
    unfold crossingSlots
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro j _
    change (if a.D.Present (physicalSlot a incoming j).1 (physicalSlot a incoming j).2 then _ else _) = _
    split_ifs
    · exact crossing_term a incoming next v j
    · rfl
  rw [hc]
  let C := fun j : Fin 20 =>
    if a.D.Present (physicalSlot a incoming j).1 (physicalSlot a incoming j).2 then
      1 + dot (v (physicalSlot a incoming j).1) (v (physicalSlot a incoming j).2) else 1
  let P := fun j : Fin 20 => if physicalSlot a incoming j ∈ originalLegs a.G then
    pinTerm a v (physicalSlot a incoming j) else 1
  have hs : (∏ j, C j) * (∏ j, P j) =
      localSlotProduct a incoming (slotField a incoming ω) v := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    exact slot_cross_pin_product a incoming ω v hv j
  change _ * _ * (∏ j, C j) * (_ * ∏ j, P j) = _
  unfold exteriorFactor
  rw [show ∀ O I OP : ℝ, O * I * (∏ j, C j) * (OP * ∏ j, P j) =
      (O * OP) * I * ((∏ j, C j) * ∏ j, P j) by intros; ring, hs]

#print axioms network_factors_cut
#print axioms exteriorFactor_nonneg

end AKLT.W.REC089
