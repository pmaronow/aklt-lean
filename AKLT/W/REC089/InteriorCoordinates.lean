module
public import AKLT.W.REC089.ExternalFields
public import AKLT.W.REC089.PatternFactorization

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC089

attribute [local instance] Classical.propDecidable

abbrev InteriorSite (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass) :=
  {x : a.D.active // insideTemplate a incoming x}

abbrev ActiveTips (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass) :=
  {t : Fin 4 // actualTipStatus a incoming t ≠ .X}

theorem core_membership (π : PatternData) {z : Plane} (hz : z ∈ coreSites π) :
    z ∈ templateSites \ templateTips ∧ π.statusAt z ≠ .X := by
  obtain ⟨ha, ht⟩ := Finset.mem_sdiff.mp hz
  obtain ⟨hs, hx⟩ := Finset.mem_filter.mp ha
  exact ⟨Finset.mem_sdiff.mpr ⟨hs, ht⟩, hx⟩

def coreInterior (a : AKLT.Blueprint.Rec.Departure) (incoming outgoing : Compass)
    (π : PatternData) (hm : Matches a incoming outgoing π) (c : coreSites π) :
    InteriorSite a incoming := by
  have hs := core_membership π c.property
  have hi : localChart a incoming c.val ∈ localSites a incoming :=
    (chart_mem_local a incoming _).mpr (Finset.mem_sdiff.mp hs.1).1
  refine ⟨⟨localChart a incoming c.val, Finset.mem_filter.mpr
    ⟨localSites_sub_G a incoming hi, ?_⟩⟩, hi⟩
  rw [← hm.2.2.1 c.val hs.1]
  exact hs.2

def tipInterior (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass)
    (t : ActiveTips a incoming) : InteriorSite a incoming := by
  have hi : localChart a incoming (tipPoint t.val) ∈ localSites a incoming :=
    (chart_mem_local a incoming _).mpr (tipPoint_mem t.val).1
  exact ⟨⟨localChart a incoming (tipPoint t.val),
    Finset.mem_filter.mpr ⟨localSites_sub_G a incoming hi, t.property⟩⟩, hi⟩

def interiorSumMap (a : AKLT.Blueprint.Rec.Departure) (incoming outgoing : Compass)
    (π : PatternData) (hm : Matches a incoming outgoing π) :
    coreSites π ⊕ ActiveTips a incoming → InteriorSite a incoming :=
  Sum.elim (coreInterior a incoming outgoing π hm) (tipInterior a incoming)

theorem interiorSumMap_injective (a : AKLT.Blueprint.Rec.Departure) (incoming outgoing : Compass)
    (π : PatternData) (hm : Matches a incoming outgoing π) :
    Function.Injective (interiorSumMap a incoming outgoing π hm) := by
  intro x y h
  have he := congrArg (fun x : InteriorSite a incoming => x.val.val) h
  have hi : Function.Injective (localChart a incoming) := (chartEquiv a incoming).injective
  cases x with
  | inl c =>
    cases y with
    | inl d => exact congrArg Sum.inl (Subtype.ext (hi he))
    | inr t =>
      have hc : c.val ∈ templateTips := (hi he) ▸ (tipPoint_mem t.val).2
      exact ((Finset.mem_sdiff.mp c.property).2 hc).elim
  | inr t =>
    cases y with
    | inl c =>
      have hc : c.val ∈ templateTips := (hi he) ▸ (tipPoint_mem t.val).2
      exact ((Finset.mem_sdiff.mp c.property).2 hc).elim
    | inr u => exact congrArg Sum.inr (Subtype.ext (tipPoint_injective (hi he)))

theorem interiorSumMap_surjective (a : AKLT.Blueprint.Rec.Departure) (incoming outgoing : Compass)
    (π : PatternData) (hm : Matches a incoming outgoing π) :
    Function.Surjective (interiorSumMap a incoming outgoing π hm) := by
  intro x
  obtain ⟨z, hz, he⟩ := Finset.mem_image.mp x.property
  have hlive : a.D.status (localChart a incoming z) ≠ .X := by
    rw [he]
    exact (Finset.mem_filter.mp x.val.property).2
  by_cases ht : z ∈ templateTips
  · obtain ⟨t, ht⟩ := tipPoint_surjective z ht
    have hl : actualTipStatus a incoming t ≠ .X := by
      unfold actualTipStatus
      rw [ht]
      exact hlive
    refine ⟨.inr ⟨t, hl⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change localChart a incoming (tipPoint t) = x.val.val
    rw [ht, he]
  · have hc : z ∈ coreSites π := by
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_filter.mpr ⟨hz, ?_⟩, ht⟩
      rw [hm.2.2.1 z (Finset.mem_sdiff.mpr ⟨hz, ht⟩)]
      exact hlive
    refine ⟨.inl ⟨z, hc⟩, ?_⟩
    exact Subtype.ext (Subtype.ext he)

def interiorSiteEquiv (a : AKLT.Blueprint.Rec.Departure) (incoming outgoing : Compass)
    (π : PatternData) (hm : Matches a incoming outgoing π) :
    InteriorSite a incoming ≃ coreSites π ⊕ ActiveTips a incoming :=
  (Equiv.ofBijective (interiorSumMap a incoming outgoing π hm)
    ⟨interiorSumMap_injective a incoming outgoing π hm,
      interiorSumMap_surjective a incoming outgoing π hm⟩).symm

@[simp] theorem interiorSiteEquiv_inl (a : AKLT.Blueprint.Rec.Departure)
    (incoming outgoing : Compass) (π : PatternData) (hm : Matches a incoming outgoing π)
    (c : coreSites π) :
    (interiorSiteEquiv a incoming outgoing π hm).symm (.inl c) =
      coreInterior a incoming outgoing π hm c := rfl

@[simp] theorem interiorSiteEquiv_inr (a : AKLT.Blueprint.Rec.Departure)
    (incoming outgoing : Compass) (π : PatternData) (hm : Matches a incoming outgoing π)
    (t : ActiveTips a incoming) :
    (interiorSiteEquiv a incoming outgoing π hm).symm (.inr t) = tipInterior a incoming t := rfl

theorem joined_interior (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass)
    (η : InteriorSpins a incoming) (ω : ExteriorSpins a incoming) (x : InteriorSite a incoming) :
    a.D.spins (joinSpins (insideTemplate a incoming) η ω) x.val.val = spinVector (η x) := by
  rw [Network.spins, dite_eq_left x.val.property]
  rw [joinSpins_inside (insideTemplate a incoming) η ω x]

def actualCoreSpins (a : AKLT.Blueprint.Rec.Departure) (incoming outgoing : Compass)
    (π : PatternData) (hm : Matches a incoming outgoing π) (η : InteriorSpins a incoming) :
    coreSites π → SpinLetter := fun c => η (coreInterior a incoming outgoing π hm c)

theorem joined_core (a : AKLT.Blueprint.Rec.Departure) (incoming outgoing : Compass)
    (π : PatternData) (hm : Matches a incoming outgoing π)
    (η : InteriorSpins a incoming) (ω : ExteriorSpins a incoming)
    {z : Plane} (hz : z ∈ templateSites \ templateTips) :
    a.D.spins (joinSpins (insideTemplate a incoming) η ω) (localChart a incoming z) =
      supportSpins (coreSites π) (actualCoreSpins a incoming outgoing π hm η) z := by
  by_cases hx : π.statusAt z = .X
  · have hactual : a.D.status (localChart a incoming z) = .X := (hm.2.2.1 z hz).symm.trans hx
    have hn : localChart a incoming z ∉ a.D.active := by simp [Network.active, hactual]
    have hc : z ∉ coreSites π := fun h => (core_membership π h).2 hx
    simp [Network.spins, supportSpins, hn, hc]
  · have hc : z ∈ coreSites π := Finset.mem_sdiff.mpr
      ⟨Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hz).1, hx⟩, (Finset.mem_sdiff.mp hz).2⟩
    exact (joined_interior a incoming η ω (coreInterior a incoming outgoing π hm ⟨z, hc⟩)).trans
      (by simp [supportSpins, hc, actualCoreSpins])

theorem core_commonStatus (a : AKLT.Blueprint.Rec.Departure) (hU : a.D.status a.y = .U)
    (incoming outgoing : Compass) (π : PatternData) (hm : Matches a incoming outgoing π)
    (next : Bool) (c : coreSites π) :
    commonStatus a next (coreInterior a incoming outgoing π hm c).val.val =
      if next ∧ c.val = (0, 0) then .D else π.statusAt c.val := by
  have hs := hm.2.2.1 c.val (core_membership π c.property).1
  have h0 : localChart a incoming (0, 0) = a.y := AKLT.W.REC096.chart_zero _ _
  have heq : localChart a incoming c.val = a.y ↔ c.val = (0, 0) := by
    rw [← h0]
    exact (chartEquiv a incoming).injective.eq_iff
  cases next
  · exact hs.symm
  · change (traceStep a.D a.y a.o).status (localChart a incoming c.val) = _
    by_cases hc : c.val = (0, 0)
    · simp [traceStep, hc, h0, hU]
    · simp [traceStep, heq, hc, hs]

theorem tip_commonStatus (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass)
    (next : Bool) (t : ActiveTips a incoming) :
    commonStatus a next (tipInterior a incoming t).val.val = actualTipStatus a incoming t.val := by
  have h0 : localChart a incoming (0, 0) = a.y := AKLT.W.REC096.chart_zero _ _
  have hn : localChart a incoming (tipPoint t.val) ≠ a.y := by
    rw [← h0]
    exact (chartEquiv a incoming).injective.ne (tip_not_center t.val)
  cases next <;> simp [commonStatus, tipInterior, traceStep, hn, actualTipStatus]

#print axioms interiorSiteEquiv
#print axioms joined_core

end AKLT.W.REC089
