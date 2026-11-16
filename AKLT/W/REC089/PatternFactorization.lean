import AKLT.W.REC089.TemplateGeometry

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC089

attribute [local instance] Classical.propDecidable

def templateBondTerm (π : PatternData) (next : Bool) (v : Plane → Vec3)
    (e : Plane × Plane) : ℝ :=
  if next ∧ ({e.1, e.2} : Finset Plane) = {(0, 0), π.outgoing.step} then 1
  else 1 + dot (v e.1) (v e.2)

theorem pattern_bond_product_split (π : PatternData) (next : Bool) (v : Plane → Vec3) :
    (∏ e ∈ π.bonds, templateBondTerm π next v e) =
      (∏ e ∈ coreBonds π, templateBondTerm π next v e) *
      ∏ t : Fin 4, if coverTipBond π t then
        1 + dot (v (tipPoint t)) (v (tipNeighbour t)) else 1 := by
  classical
  calc
    _ = (∏ e ∈ coreBonds π, templateBondTerm π next v e) *
        ∏ e ∈ ((Finset.univ.filter fun t => coverTipBond π t = true).image tipEdge),
          templateBondTerm π next v e := by
      conv_lhs => rw [pattern_bonds_split π, Finset.prod_union (pattern_bonds_disjoint π)]
    _ = _ := by
      congr 1
      rw [Finset.prod_image (fun _ _ _ _ h => tipEdge_injective h), Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro t _
      by_cases h : coverTipBond π t = true
      · simp only [h, ite_true, templateBondTerm, tipEdge_not_dropped, and_false, ite_false]
        rcases tipEdge_endpoints t with he | he <;> rw [he]
        · rw [dot_comm]
      · simp [h]

theorem pattern_slot_product_split (π : PatternData) (hπ : π.Covered)
    (c : Fin 8 → Vec3) (b : Fin 4 → Fin 3 → Vec3) (v : Plane → Vec3) :
    (∏ j : Fin 20, if π.statusAt (externalSlot j).1 = .X then 1 else
      1 + dot (packFields c b j) (v (externalSlot j).1)) =
      (∏ j : Fin 8, if π.statusAt (externalSlot (cornerIndex j)).1 = .X then 1 else
        1 + dot (c j) (v (externalSlot (cornerIndex j)).1)) *
      ∏ t : Fin 4, tipExternal (b t) (v (tipPoint t)) := by
  rw [prod_slots]
  simp_rw [packFields_corner]
  congr 1
  apply Finset.prod_congr rfl
  intro t _
  unfold tipExternal
  apply Finset.prod_congr rfl
  intro j _
  rw [packFields_tip, tip_slot_site, hπ.2.2.2.2.2.2.2.2.1 _ (tipPoint_mem t).2]
  simp only [show Status.U ≠ .X from by decide, ite_false]
  rw [dot_comm]

def patternCoreSpins (π : PatternData) (hπ : π.Covered)
    (n : π.active → SpinLetter) : coreSites π → SpinLetter :=
  fun c => n ((patternSiteEquiv π hπ).symm (.inl c))

theorem pattern_spins_core (π : PatternData) (hπ : π.Covered)
    (n : π.active → SpinLetter) {x : Plane} (hx : x ∉ templateTips) :
    π.spins n x = supportSpins (coreSites π) (patternCoreSpins π hπ n) x := by
  by_cases ha : x ∈ π.active
  · have hc : x ∈ coreSites π := Finset.mem_sdiff.mpr ⟨ha, hx⟩
    simp [PatternData.spins, supportSpins, ha, hc, patternCoreSpins,
      patternSiteEquiv]
  · have hc : x ∉ coreSites π := fun h => ha (Finset.mem_sdiff.mp h).1
    simp [PatternData.spins, supportSpins, ha, hc]

theorem pattern_spins_tip (π : PatternData) (hπ : π.Covered)
    (n : π.active → SpinLetter) (t : Fin 4) :
    π.spins n (tipPoint t) =
      spinVector (n ((patternSiteEquiv π hπ).symm (.inr t))) := by
  simp [PatternData.spins, pattern_tip_active π hπ t, patternSiteEquiv]

def patternCoreFactors (π : PatternData) (next : Bool) (c : Fin 8 → Vec3)
    (σ : coreSites π → SpinLetter) : ℝ :=
  (∏ e ∈ coreBonds π, templateBondTerm π next (supportSpins (coreSites π) σ) e) *
    cornerKernel π c σ

def patternTipFactor (π : PatternData) (b : Fin 4 → Fin 3 → Vec3)
    (σ : coreSites π → SpinLetter) (t : Fin 4) (d : SpinLetter) : ℝ :=
  (if coverTipBond π t then
    1 + dot (spinVector d) (supportSpins (coreSites π) σ (tipNeighbour t)) else 1) *
      tipExternal (b t) (spinVector d)

theorem pattern_factors_separate (π : PatternData) (hπ : π.Covered) (next : Bool)
    (c : Fin 8 → Vec3) (b : Fin 4 → Fin 3 → Vec3) (n : π.active → SpinLetter) :
    ((∏ e ∈ π.bonds, templateBondTerm π next (π.spins n) e) *
      ∏ j : Fin 20, if π.statusAt (externalSlot j).1 = .X then 1 else
        1 + dot (packFields c b j) (π.spins n (externalSlot j).1)) =
      patternCoreFactors π next c (patternCoreSpins π hπ n) *
        ∏ t, patternTipFactor π b (patternCoreSpins π hπ n) t
          (n ((patternSiteEquiv π hπ).symm (.inr t))) := by
  rw [pattern_bond_product_split, pattern_slot_product_split π hπ]
  have hb : (∏ e ∈ coreBonds π, templateBondTerm π next (π.spins n) e) =
      ∏ e ∈ coreBonds π, templateBondTerm π next
        (supportSpins (coreSites π) (patternCoreSpins π hπ n)) e := by
    apply Finset.prod_congr rfl
    intro e he
    have h := (Finset.mem_filter.mp he).2
    unfold templateBondTerm
    rw [pattern_spins_core π hπ n h.1, pattern_spins_core π hπ n h.2]
  have hc : (∏ j : Fin 8, if π.statusAt (externalSlot (cornerIndex j)).1 = .X then 1
        else 1 + dot (c j) (π.spins n (externalSlot (cornerIndex j)).1)) =
      cornerKernel π c (patternCoreSpins π hπ n) := by
    unfold cornerKernel
    apply Finset.prod_congr rfl
    intro j _
    rw [pattern_spins_core π hπ n (Finset.mem_sdiff.mp (corner_slot_core j)).2]
  rw [hb, hc]
  unfold patternCoreFactors patternTipFactor
  rw [Finset.prod_mul_distrib]
  simp_rw [pattern_spins_tip π hπ n,
    pattern_spins_core π hπ n (Finset.mem_sdiff.mp (tipNeighbour_mem _)).2]
  ring

/-- Integrate all four U tips while retaining both external slots at each corner. -/
theorem pattern_tip_factorization (π : PatternData) (hπ : π.Covered)
    (c : Fin 8 → Vec3) (b : Fin 4 → Fin 3 → Vec3) (next : Bool) :
    ballPatternFunctional π next (packFields c b) = coveredReduced π c b next := by
  let e := patternSiteEquiv π hπ
  let w := fun (x : π.active) (d : SpinLetter) =>
    spinWeight (if next ∧ x.val = (0, 0) then .D else π.statusAt x.val) d
  have hf := sum_eliminate_leaves e w (patternCoreFactors π next c) (patternTipFactor π b)
  have hleft : ballPatternFunctional π next (packFields c b) =
      ∑ n : π.active → SpinLetter, (∏ x, w x (n x)) *
        patternCoreFactors π next c (fun x => n (e.symm (.inl x))) *
        ∏ t, patternTipFactor π b (fun x => n (e.symm (.inl x))) t
          (n (e.symm (.inr t))) := by
    unfold ballPatternFunctional
    apply Finset.sum_congr rfl
    intro n _
    have h := pattern_factors_separate π hπ next c b n
    unfold patternCoreSpins at h
    simpa only [w, e, templateBondTerm, mul_assoc] using
      congrArg (fun q => (∏ x, w x (n x)) * q) h
  rw [hleft, hf]
  unfold coveredReduced
  apply Finset.sum_congr rfl
  intro σ _
  have ht (t : Fin 4) : (∑ d : SpinLetter, w (e.symm (.inr t)) d *
      patternTipFactor π b σ t d) =
      coveredTipValue (coverTipBond π t) (b t)
        (supportSpins (coreSites π) σ (tipNeighbour t)) := by
    unfold coveredTipValue siteFunctional patternTipFactor
    apply Finset.sum_congr rfl
    intro d _
    have hw : w (e.symm (.inr t)) d = spinWeight .U d := by
      change spinWeight (if next ∧ tipPoint t = (0, 0) then .D
        else π.statusAt (tipPoint t)) d = _
      simp only [tip_not_centre t, and_false, ite_false,
        hπ.2.2.2.2.2.2.2.2.1 _ (tipPoint_mem t).2]
    rw [hw]
  simp_rw [ht]
  change (∏ x : coreSites π, spinWeight
      (if next ∧ x.val = (0, 0) then .D else π.statusAt x.val) (σ x)) *
      patternCoreFactors π next c σ * _ = _
  unfold patternCoreFactors coreKernel templateBondTerm
  ring

#print axioms pattern_factors_separate
#print axioms pattern_tip_factorization

end AKLT.W.REC089
