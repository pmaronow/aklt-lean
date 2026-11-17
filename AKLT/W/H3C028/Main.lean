module
public import AKLT.W.H3C025.Main
public import AKLT.W.H3C026.Main
public import AKLT.W.H3C027.Main

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Gen.Packed AKLT.Cert.H3 AKLT.Cert.H3.Production
set_option maxRecDepth 100000

namespace AKLT.W.H3C028

private theorem planeCheck_fields (G : Graph) (T : Tables) (X : PairType)
    (d₀ : Compass) (key : Nat)
    (h : planeCheck G T X d₀ key = true) :
    localRowCheck G.quotient T.planeFn T.capFn X d₀ (phase (key / 3741))
        (finState (key % 3741)) = true ∧
    packedRowCheck 79 19881 26 1
      (repeatLane 80 19881 (T.cap key)) [(1, T.plane key)] = true ∧
    0 < T.cap key ∧ T.cap key < 2^26 ∧
    (key / 3741 < 2 ∨ 65536 ≤ T.cap key) ∧
    lane (T.plane key) 80 (siteIndex kernelCentre) = 0 ∧
    lane (T.plane key) 80 (siteIndex (kernelTarget X)) =
      (if key / 3741 < 2 then 0 else 65536) ∧
    freeRow G T (key / 3741) (key % 3741) ≤ coefficientScale * T.cap key := by
  simp only [planeCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨h.1.1.1.1.1.1.1, h.1.1.1.1.1.1.2,
    h.1.1.1.1.1.2.1, h.1.1.1.1.1.2.2, h.1.1.1.1.2,
    h.1.1.1.2, h.1.1.2, h.1.2⟩

private theorem decodePhaseKey (φ : Phase) (a : Fin 3741) :
    phase (phaseKey (phaseCode φ) a.val / 3741) = φ ∧
      finState (phaseKey (phaseCode φ) a.val % 3741) = a := by
  have hdiv : (phaseCode φ * 3741 + a.val) / 3741 = phaseCode φ := by
    cases φ <;> simp [phaseCode] <;> omega
  have hmod : (phaseCode φ * 3741 + a.val) % 3741 = a.val := by
    cases φ <;> simp [phaseCode] <;> omega
  constructor
  · change phase ((phaseCode φ * 3741 + a.val) / 3741) = φ
    rw [hdiv]
    cases φ <;> rfl
  · change finState ((phaseCode φ * 3741 + a.val) % 3741) = a
    rw [hmod]
    apply Fin.ext
    simp [finState, Nat.mod_eq_of_lt a.isLt]

theorem tableBoundsLeaf : CertData.H3.Bridge.TableBoundsLeaf := AKLT.W.H3C025.main

private theorem siteIndex_lt_radius {x : Plane}
    (hx : x ∈ square (0,0) certificateRadius) : siteIndex x < 19881 := by
  have hx' : (-70 ≤ x.1 ∧ x.1 ≤ 70) ∧ -70 ≤ x.2 ∧ x.2 ≤ 70 := by
    simpa [square, certificateRadius] using hx
  let r := (x.1 + 70).toNat
  let c := (x.2 + 70).toNat
  have hr0 : 0 ≤ x.1 + 70 := by omega
  have hc0 : 0 ≤ x.2 + 70 := by omega
  have hrI : (r : Int) = x.1 + 70 := Int.toNat_of_nonneg hr0
  have hcI : (c : Int) = x.2 + 70 := Int.toNat_of_nonneg hc0
  have hr : r ≤ 140 := by omega
  have hc : c ≤ 140 := by omega
  change r * 141 + c < 19881
  omega

private theorem gridSite_siteIndex {x : Plane}
    (hx : x ∈ square (0,0) certificateRadius) : gridSite (siteIndex x) = x := by
  have hx' : (-70 ≤ x.1 ∧ x.1 ≤ 70) ∧ -70 ≤ x.2 ∧ x.2 ≤ 70 := by
    simpa [square, certificateRadius] using hx
  let r := (x.1 + 70).toNat
  let c := (x.2 + 70).toNat
  have hr0 : 0 ≤ x.1 + 70 := by omega
  have hc0 : 0 ≤ x.2 + 70 := by omega
  have hrI : (r : Int) = x.1 + 70 := Int.toNat_of_nonneg hr0
  have hcI : (c : Int) = x.2 + 70 := Int.toNat_of_nonneg hc0
  have hc : c < 141 := by omega
  have hdiv : (r * 141 + c) / 141 = r := by omega
  have hmod : (r * 141 + c) % 141 = c := by omega
  unfold gridSite siteIndex
  apply Prod.ext
  · change ((r * 141 + c) / 141 : Nat) - (70 : Int) = x.1
    rw [hdiv]
    omega
  · change ((r * 141 + c) % 141 : Nat) - (70 : Int) = x.2
    rw [hmod]
    omega

private theorem target_mem_square (X : PairType) :
    kernelTarget X ∈ square (0,0) certificateRadius := by
  cases X <;> simp [square, kernelTarget, certificateRadius, Finset.mem_product,
    Finset.mem_Icc]

private theorem centre_mem_square :
    kernelCentre ∈ square (0,0) certificateRadius := by
  simp [square, kernelCentre, certificateRadius, Finset.mem_product, Finset.mem_Icc]

private theorem repeatedLane_value (z s : Nat) (hz : z < 2^80) (hs : s < 19881) :
    lane (repeatLane 80 19881 z) 80 s = z := by
  rw [repeatLane_eq 80 19881 z (by omega)]
  rw [lane_packFn _ _ _ (by intro i hi; exact hz)]
  simp [hs]

private theorem extended_eq_value {q : Nat} (C : StationaryData q)
    (φ : Phase) (a : Fin q) (x : Plane) (hx : x ∈ square (0,0) certificateRadius) :
    C.extended φ a x = C.value φ a ⟨x,hx⟩ := by
  unfold StationaryData.extended
  rw [dite_eq_left hx]

/-- Acceptance of a production plane proves every clause of the V2 plane specification. -/
theorem main : CertData.H3.Bridge.PlaneSoundLeaf := by
  intro G T X d₀ hQ hBounds hCase φ a hcheck
  have hf := planeCheck_fields G T X d₀ (phaseKey (phaseCode φ) a.val) hcheck
  rcases hf with ⟨hlocal, hpack, hcapPos, hcapLt, hphaseCap, hcenter,
    htarget, hfreeCheck⟩
  have hkey := decodePhaseKey φ a
  have hdiv : phaseKey (phaseCode φ) a.val / 3741 = phaseCode φ := by
    cases φ <;> simp [phaseKey, phaseCode] <;> omega
  have hmod : phaseKey (phaseCode φ) a.val % 3741 = a.val := by
    cases φ <;> simp [phaseKey, phaseCode] <;> omega
  have hpos : 0 < T.capFn φ a := by
    simpa [Tables.capFn, phaseKey, phaseCode] using hcapPos
  have hthreshold : (φ = .C ∨ φ = .D) → certificateValueScale ≤ T.capFn φ a := by
    intro hCD
    rw [hdiv] at hphaseCap
    cases φ <;> simp_all [Tables.capFn, phaseKey, phaseCode, certificateValueScale]
  have hfreeCheck' := hfreeCheck
  rw [hdiv, hmod] at hfreeCheck'
  have hfreeBound : freeRow G T (phaseCode φ) a.val ≤
      coefficientScale * T.capFn φ a := by
    simpa [Tables.capFn, phaseKey, phaseCode] using hfreeCheck'
  have hfreeFinal :
      (∑ d : Compass, ∑ ψ : Phase,
        coefficientCeiling (freeCoefficient G.quotient φ a d ψ) *
          T.capFn ψ (G.quotient.successor a d)) ≤
        certificateCoefficientScale * T.capFn φ a := by
    calc
      _ = freeRow G T (phaseCode φ) a.val := (AKLT.W.H3C027.main G T hQ φ a).symm
      _ ≤ coefficientScale * T.capFn φ a := hfreeBound
      _ = certificateCoefficientScale * T.capFn φ a := by
        norm_num [coefficientScale, certificateCoefficientScale]
  have hvalue : ∀ x : square (0,0) certificateRadius,
      T.data.value φ a x ≤ T.capFn φ a := by
    intro x
    let s := siteIndex x.val
    have hs : s < 19881 := siteIndex_lt_radius x.property
    have hz : T.cap (phaseKey (phaseCode φ) a.val) < 2^80 := by
      have := hcapLt
      omega
    have hrow := packedRowCheck_sound hpack s hs
    have hrep := repeatedLane_value (T.cap (phaseKey (phaseCode φ) a.val)) s hz hs
    have hrow' : lane (T.plane (phaseKey (phaseCode φ) a.val)) 80 s ≤
        T.cap (phaseKey (phaseCode φ) a.val) := by
      simpa [component, hrep] using hrow
    simpa [Tables.data, Tables.planeFn, Tables.capFn, phaseKey, phaseCode] using hrow'
  have hterminal :
      (T.data.extended φ a kernelCentre = 0 ∧
        (T.data.extended φ a (kernelTarget X) : ℚ) =
          certificateValueScale * phaseTerminal φ) := by
    have hcVal : T.data.value φ a ⟨kernelCentre, centre_mem_square⟩ = 0 := by
      simpa [Tables.data, Tables.planeFn, phaseKey, phaseCode, siteIndex] using hcenter
    have htVal : T.data.value φ a ⟨kernelTarget X, target_mem_square X⟩ =
        certificateValueScale * phaseTerminal φ := by
      have hraw := htarget
      rw [hdiv] at hraw
      have hraw' : lane (T.planeFn φ a) 80 (siteIndex (kernelTarget X)) =
          (if phaseCode φ < 2 then 0 else 65536) := by
        simpa [Tables.planeFn, phaseKey, phaseCode] using hraw
      change (lane (T.planeFn φ a) 80 (siteIndex (kernelTarget X)) : ℚ) = _
      rw [hraw']
      cases φ <;> norm_num [phaseCode, phaseTerminal, certificateValueScale]
    constructor
    · rw [extended_eq_value T.data φ a kernelCentre centre_mem_square]
      exact hcVal
    · rw [extended_eq_value T.data φ a (kernelTarget X) (target_mem_square X)]
      exact htVal
  have hlocalRows := AKLT.W.H3C026.main G T X d₀ hQ hBounds hCase
  refine ⟨hpos, hthreshold, hfreeFinal, hvalue, hterminal, ?_⟩
  intro x hxCentre hxTarget
  let s := siteIndex x.val
  have hs : s < 19881 := siteIndex_lt_radius x.property
  have hgrid : gridSite s = x.val := gridSite_siteIndex x.property
  have hsCentre : gridSite s ≠ kernelCentre := by simpa [hgrid] using hxCentre
  have hsTarget : gridSite s ≠ kernelTarget X := by simpa [hgrid] using hxTarget
  have hlocal' := hlocal
  rw [hkey.1, hkey.2] at hlocal'
  have hrow := hlocalRows φ a s hs hsCentre hsTarget
  have hcheckRow : component 80 s
      (rowTerms G.quotient T.planeFn T.capFn X d₀ φ a) ≤
      coefficientScale * lane (T.planeFn φ a) 80 s :=
    localRowCheck_sound hlocal' s hs
  rw [hrow] at hcheckRow
  simpa [Tables.data, Tables.planeFn, certificateCoefficientScale, coefficientScale,
    s, hgrid] using hcheckRow

#print axioms tableBoundsLeaf
#print axioms main

end AKLT.W.H3C028
