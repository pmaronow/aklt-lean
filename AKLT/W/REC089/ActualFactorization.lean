import AKLT.W.REC089.FibreFactors
import AKLT.W.REC089.InteriorCoordinates

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC089

attribute [local instance] Classical.propDecidable

def cornerFields (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass)
    (ω : ExteriorSpins a incoming) (j : Fin 8) : Vec3 :=
  slotField a incoming ω (cornerIndex j)

def tipFields (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass)
    (ω : ExteriorSpins a incoming) (t : Fin 4) (j : Fin 3) : Vec3 :=
  slotField a incoming ω (tipIndex t j)

theorem prod_activeTips (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass)
    (F : Fin 4 → ℝ) (hF : ∀ t, actualTipStatus a incoming t = .X → F t = 1) :
    (∏ t : Fin 4, F t) = ∏ t : ActiveTips a incoming, F t.val := by
  let S := Finset.univ.filter fun t => actualTipStatus a incoming t ≠ .X
  have h : (∏ t ∈ S, F t) = ∏ t : Fin 4, F t := by
    apply Finset.prod_subset (Finset.filter_subset _ _)
    intro t _ hn
    apply hF t
    simpa [S] using hn
  rw [← h]
  exact Finset.prod_subtype S (fun t => by simp [S]) F

theorem actual_slots_separate (a : AKLT.Blueprint.Rec.Departure) (incoming outgoing : Compass)
    (π : PatternData) (hm : Matches a incoming outgoing π) (ω : ExteriorSpins a incoming)
    (η : InteriorSpins a incoming) :
    localSlotProduct a incoming (slotField a incoming ω)
      (a.D.spins (joinSpins (insideTemplate a incoming) η ω)) =
      cornerKernel π (cornerFields a incoming ω) (actualCoreSpins a incoming outgoing π hm η) *
        ∏ t : ActiveTips a incoming,
          tipExternal (tipFields a incoming ω t.val) (spinVector (η (tipInterior a incoming t))) := by
  let v := a.D.spins (joinSpins (insideTemplate a incoming) η ω)
  unfold localSlotProduct
  rw [prod_slots]
  have hc : (∏ j : Fin 8,
      if a.D.status (physicalSlot a incoming (cornerIndex j)).1 = .X then 1
      else 1 + dot (slotField a incoming ω (cornerIndex j))
        (v (physicalSlot a incoming (cornerIndex j)).1)) =
      cornerKernel π (cornerFields a incoming ω) (actualCoreSpins a incoming outgoing π hm η) := by
    unfold cornerKernel
    apply Finset.prod_congr rfl
    intro j _
    change (if a.D.status (localChart a incoming (externalSlot (cornerIndex j)).1) = .X then 1
      else 1 + dot (slotField a incoming ω (cornerIndex j))
        (a.D.spins (joinSpins (insideTemplate a incoming) η ω)
          (localChart a incoming (externalSlot (cornerIndex j)).1))) = _
    rw [← hm.2.2.1 _ (corner_slot_core j)]
    rw [joined_core a incoming outgoing π hm η ω (corner_slot_core j)]
    rfl
  rw [hc]
  congr 1
  have ht : (∏ t : Fin 4, ∏ j : Fin 3,
      if a.D.status (physicalSlot a incoming (tipIndex t j)).1 = .X then 1
      else 1 + dot (slotField a incoming ω (tipIndex t j))
        (v (physicalSlot a incoming (tipIndex t j)).1)) =
      ∏ t : Fin 4, if actualTipStatus a incoming t = .X then 1
        else tipExternal (tipFields a incoming ω t) (v (localChart a incoming (tipPoint t))) := by
    apply Finset.prod_congr rfl
    intro t _
    by_cases hx : actualTipStatus a incoming t = .X
    · simp only [hx, ite_true]
      apply Finset.prod_eq_one
      intro j _
      change (if a.D.status (localChart a incoming (externalSlot (tipIndex t j)).1) = .X then 1
        else _) = 1
      rw [tip_slot_site]
      exact ite_eq_left hx
    · unfold tipExternal
      simp only [hx, ite_false]
      apply Finset.prod_congr rfl
      intro j _
      dsimp only [physicalSlot, slotEdge]
      change (if a.D.status (localChart a incoming (externalSlot (tipIndex t j)).1) = .X then 1
        else _) = _
      rw [tip_slot_site]
      simp only [show a.D.status (localChart a incoming (tipPoint t)) ≠ .X from hx, ite_false]
      rw [dot_comm]
      rfl
  rw [ht, prod_activeTips a incoming _ (fun t hx => by simp [hx])]
  apply Finset.prod_congr rfl
  intro t _
  simp only [t.property, ite_false]
  rw [show v (localChart a incoming (tipPoint t.val)) = spinVector (η (tipInterior a incoming t)) from
    joined_interior a incoming η ω (tipInterior a incoming t)]

def actualTipFactor (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass)
    (π : PatternData) (b : Fin 4 → Fin 3 → Vec3)
    (σ : coreSites π → SpinLetter) (t : ActiveTips a incoming) (d : SpinLetter) : ℝ :=
  (if actualTipBond a incoming t.val then
    1 + dot (spinVector d) (supportSpins (coreSites π) σ (tipNeighbour t.val)) else 1) *
      tipExternal (b t.val) (spinVector d)

theorem actual_factors_separate (a : AKLT.Blueprint.Rec.Departure) (hU : a.D.status a.y = .U)
    (incoming outgoing : Compass) (ho : a.o = a.y + outgoing.step)
    (π : PatternData) (hm : Matches a incoming outgoing π) (ω : ExteriorSpins a incoming)
    (η : InteriorSpins a incoming) (next : Bool) :
    commonFactors a next (joinSpins (insideTemplate a incoming) η ω) =
      exteriorFactor a incoming ω *
        patternCoreFactors π next (cornerFields a incoming ω) (actualCoreSpins a incoming outgoing π hm η) *
        ∏ t : ActiveTips a incoming, actualTipFactor a incoming π (tipFields a incoming ω)
          (actualCoreSpins a incoming outgoing π hm η) t (η (tipInterior a incoming t)) := by
  let v := a.D.spins (joinSpins (insideTemplate a incoming) η ω)
  rw [commonFactors, network_factors_cut a hU incoming ω next v
    (fun x hx => joined_exterior a incoming η ω hx),
    inside_bond_product a incoming outgoing ho π hm, actual_slots_separate a incoming outgoing π hm]
  have hc : (∏ e ∈ coreBonds π,
      templateBondTerm π next (fun z => v (localChart a incoming z)) e) =
      ∏ e ∈ coreBonds π, templateBondTerm π next
        (supportSpins (coreSites π) (actualCoreSpins a incoming outgoing π hm η)) e := by
    apply Finset.prod_congr rfl
    intro e he
    have h := Finset.mem_filter.mp he
    have hs := pattern_bond_active π h.1
    unfold templateBondTerm
    dsimp only [v]
    rw [joined_core a incoming outgoing π hm η ω
      (Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hs.1).1, h.2.1⟩),
      joined_core a incoming outgoing π hm η ω
      (Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hs.2).1, h.2.2⟩)]
  have ht : (∏ t : Fin 4, if actualTipBond a incoming t then
      1 + dot (v (localChart a incoming (tipPoint t))) (v (localChart a incoming (tipNeighbour t)))
        else 1) =
      ∏ t : ActiveTips a incoming, if actualTipBond a incoming t.val then
        1 + dot (spinVector (η (tipInterior a incoming t)))
          (supportSpins (coreSites π) (actualCoreSpins a incoming outgoing π hm η) (tipNeighbour t.val))
        else 1 := by
    rw [prod_activeTips a incoming _ (by
      intro t hx
      have hn : actualTipBond a incoming t ≠ true := fun hp => actual_tip_live a incoming t hp hx
      simp [hn])]
    apply Finset.prod_congr rfl
    intro t _
    rw [show v (localChart a incoming (tipPoint t.val)) = spinVector (η (tipInterior a incoming t)) from
      joined_interior a incoming η ω (tipInterior a incoming t)]
    dsimp only [v]
    rw [joined_core a incoming outgoing π hm η ω (tipNeighbour_mem t.val)]
  rw [hc, ht]
  unfold patternCoreFactors actualTipFactor
  rw [Finset.prod_mul_distrib]
  ring

#print axioms actual_slots_separate
#print axioms actual_factors_separate

end AKLT.W.REC089
