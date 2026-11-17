module
public import AKLT.W.REC089.CutBonds

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC089

attribute [local instance] Classical.propDecidable

def exteriorSpin (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass)
    (ω : ExteriorSpins a incoming) (x : Plane) : Vec3 :=
  if hx : x ∈ a.D.active then
    if hi : x ∉ localSites a incoming then spinVector (ω ⟨⟨x, hx⟩, hi⟩) else 0
  else 0

theorem exteriorSpin_ball (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass)
    (ω : ExteriorSpins a incoming) (x : Plane) : normSq (exteriorSpin a incoming ω x) ≤ 1 := by
  unfold exteriorSpin
  split_ifs <;> first | exact spin_ball _ | norm_num [normSq, dot]

theorem joined_exterior (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass)
    (η : InteriorSpins a incoming) (ω : ExteriorSpins a incoming) {x : Plane}
    (hx : x ∉ localSites a incoming) :
    a.D.spins (joinSpins (insideTemplate a incoming) η ω) x = exteriorSpin a incoming ω x := by
  by_cases ha : x ∈ a.D.active
  · have hj := joinSpins_outside (insideTemplate a incoming) η ω ⟨⟨x, ha⟩, hx⟩
    rw [Network.spins, dite_eq_left ha, hj]
    rw [exteriorSpin, dite_eq_left ha, dite_eq_left hx]
  · simp [Network.spins, exteriorSpin, ha]

def pinField (a : AKLT.Blueprint.Rec.Departure) (e : Plane × Plane) : Vec3 :=
  if he : e ∈ originalLegs a.G then (a.τ ⟨e, he⟩).val else 0

theorem pinField_ball (a : AKLT.Blueprint.Rec.Departure) (e : Plane × Plane) :
    normSq (pinField a e) ≤ 1 := by
  unfold pinField
  split_ifs
  · exact le_of_eq (a.τ _).property
  · norm_num [normSq, dot]

def physicalSlot (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass)
    (j : Fin 20) : Plane × Plane :=
  (localChart a incoming (slotEdge j).1, localChart a incoming (slotEdge j).2)

theorem physicalSlot_injective (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass) :
    Function.Injective (physicalSlot a incoming) := by
  intro i j h
  apply slotEdge_injective
  apply Prod.ext
  · exact (chartEquiv a incoming).injective (congrArg Prod.fst h)
  · exact (chartEquiv a incoming).injective (congrArg Prod.snd h)

theorem physicalSlot_facts (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass) (j : Fin 20) :
    (physicalSlot a incoming j).1 ∈ localSites a incoming ∧
      (physicalSlot a incoming j).2 ∉ localSites a incoming ∧
      Adjacent (physicalSlot a incoming j).1 (physicalSlot a incoming j).2 :=
  ⟨(chart_mem_local a incoming _).mpr (slotEdge_facts j).1,
    fun h => (slotEdge_facts j).2.1 ((chart_mem_local a incoming _).mp h),
    (AKLT.W.REC096.chart_adjacent _ _ _ _).mpr (slotEdge_facts j).2.2⟩

theorem leg_facts {G : Finset Plane} {e : Plane × Plane} (he : e ∈ originalLegs G) :
    e.1 ∈ G ∧ e.2 ∉ G ∧ Adjacent e.1 e.2 := by
  obtain ⟨x, hx, hE⟩ := Finset.mem_biUnion.mp he
  obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp hE
  cases heq
  exact ⟨hx, (Finset.mem_sdiff.mp hz).2,
    (AKLT.W.REC096.adjacent_iff _ _).mpr (Finset.mem_sdiff.mp hz).1⟩

theorem local_legs_image (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass) :
    (originalLegs a.G).filter (fun e => e.1 ∈ localSites a incoming) =
      (Finset.univ.filter fun j => physicalSlot a incoming j ∈ originalLegs a.G).image
        (physicalSlot a incoming) := by
  ext e
  constructor
  · intro he
    obtain ⟨he, hi⟩ := Finset.mem_filter.mp he
    obtain ⟨z, hz, he1⟩ := Finset.mem_image.mp hi
    let t := (chartEquiv a incoming).symm e.2
    have ht : localChart a incoming t = e.2 := (chartEquiv a incoming).apply_symm_apply _
    have htn : t ∉ templateSites := by
      intro h
      have := localSites_sub_G a incoming ((chart_mem_local a incoming t).mpr h)
      rw [ht] at this
      exact (leg_facts he).2.1 this
    have hadj : Adjacent z t := by
      apply (AKLT.W.REC096.chart_adjacent a.y z t incoming).mp
      change Adjacent (localChart a incoming z) (localChart a incoming t)
      rw [he1, ht]
      exact (leg_facts he).2.2
    obtain ⟨j, hj⟩ := boundary_slot_exists hz htn hadj
    have heq : physicalSlot a incoming j = e := by
      simp only [physicalSlot, hj, he1, ht]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, heq ▸ he⟩, heq⟩
  · intro he
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).2, (physicalSlot_facts a incoming j).1⟩

def pinTerm (a : AKLT.Blueprint.Rec.Departure) (v : Plane → Vec3)
    (e : Plane × Plane) : ℝ :=
  if e.1 ∈ a.D.active then 1 + dot (pinField a e) (v e.1) else 1

def outsidePinProduct (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass)
    (v : Plane → Vec3) : ℝ :=
  ∏ e ∈ (originalLegs a.G).filter (fun e => e.1 ∉ localSites a incoming), pinTerm a v e

theorem pin_product_as_finset (a : AKLT.Blueprint.Rec.Departure) (v : Plane → Vec3) :
    (∏ e : originalLegs a.G, if e.val.1 ∈ a.D.active then
      1 + dot (a.τ e).val (v e.val.1) else 1) = ∏ e ∈ originalLegs a.G, pinTerm a v e := by
  rw [← Finset.prod_coe_sort (originalLegs a.G) (pinTerm a v)]
  apply Finset.prod_congr rfl
  intro e _
  simp [pinTerm, pinField, e.property]

theorem pin_product_cut (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass)
    (v : Plane → Vec3) :
    (∏ e : originalLegs a.G, if e.val.1 ∈ a.D.active then
      1 + dot (a.τ e).val (v e.val.1) else 1) =
      outsidePinProduct a incoming v *
      ∏ j : Fin 20, if physicalSlot a incoming j ∈ originalLegs a.G then
        pinTerm a v (physicalSlot a incoming j) else 1 := by
  rw [pin_product_as_finset]
  rw [← Finset.prod_filter_mul_prod_filter_not (originalLegs a.G)
    (fun e => e.1 ∉ localSites a incoming)]
  simp only [not_not]
  change outsidePinProduct a incoming v *
    (∏ e ∈ (originalLegs a.G).filter (fun e => e.1 ∈ localSites a incoming), pinTerm a v e) = _
  congr 1
  rw [local_legs_image a incoming]
  rw [Finset.prod_image (f := pinTerm a v)
    (fun _ _ _ _ h => physicalSlot_injective a incoming h)]
  rw [Finset.prod_filter]

def slotField (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass)
    (ω : ExteriorSpins a incoming) (j : Fin 20) : Vec3 :=
  if physicalSlot a incoming j ∈ originalLegs a.G then pinField a (physicalSlot a incoming j)
  else if a.D.Present (physicalSlot a incoming j).1 (physicalSlot a incoming j).2 then
    exteriorSpin a incoming ω (physicalSlot a incoming j).2 else 0

theorem slotField_ball (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass)
    (ω : ExteriorSpins a incoming) (j : Fin 20) : normSq (slotField a incoming ω j) ≤ 1 := by
  unfold slotField
  split_ifs
  · exact pinField_ball _ _
  · exact exteriorSpin_ball _ _ _ _
  · norm_num [normSq, dot]

theorem slot_cross_pin_product (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass)
    (ω : ExteriorSpins a incoming) (v : Plane → Vec3)
    (hv : ∀ x, x ∉ localSites a incoming → v x = exteriorSpin a incoming ω x) (j : Fin 20) :
    (if a.D.Present (physicalSlot a incoming j).1 (physicalSlot a incoming j).2 then
      1 + dot (v (physicalSlot a incoming j).1) (v (physicalSlot a incoming j).2) else 1) *
      (if physicalSlot a incoming j ∈ originalLegs a.G then
        pinTerm a v (physicalSlot a incoming j) else 1) =
      if a.D.status (physicalSlot a incoming j).1 = .X then 1
      else 1 + dot (slotField a incoming ω j) (v (physicalSlot a incoming j).1) := by
  have hg := localSites_sub_G a incoming (physicalSlot_facts a incoming j).1
  have ha : (physicalSlot a incoming j).1 ∈ a.D.active ↔
      a.D.status (physicalSlot a incoming j).1 ≠ .X := by simp [Network.active, hg]
  have hno (hp : a.D.Present (physicalSlot a incoming j).1 (physicalSlot a incoming j).2) :
      physicalSlot a incoming j ∉ originalLegs a.G := by
    intro he
    exact (leg_facts he).2.1 (Finset.mem_filter.mp hp.2.1).1
  by_cases hs : a.D.status (physicalSlot a incoming j).1 = .X
  · have hn : ¬ a.D.Present (physicalSlot a incoming j).1 (physicalSlot a incoming j).2 :=
      fun hp => (ha.mp hp.1) hs
    simp [hs, hn, pinTerm, ha]
  · by_cases hp : a.D.Present (physicalSlot a incoming j).1 (physicalSlot a incoming j).2
    · simp only [hp, ite_true, hno hp, ite_false, hs, slotField, one_mul, mul_one]
      rw [hv _ (physicalSlot_facts a incoming j).2.1, dot_comm]
    · by_cases hl : physicalSlot a incoming j ∈ originalLegs a.G
      · simp [hp, hl, pinTerm, ha, hs, slotField]
      · simp [hp, hl, hs, slotField, dot_zero_left]

#print axioms pin_product_cut
#print axioms slot_cross_pin_product

end AKLT.W.REC089
