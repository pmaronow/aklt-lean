import AKLT.Blueprint.H1.NodesPassage

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.H1M007

private def retainedSites (π : PatternData) : Finset Plane :=
  π.active.erase (0, 0)

private def lexSites (π : PatternData) : Finset (Lex Plane) :=
  (retainedSites π).map ⟨toLex, toLex.injective⟩

private def siteOrderIso (π : PatternData) : Fin (retainedSites π).card ≃o ↥(lexSites π) :=
  Finset.orderIsoOfFin (lexSites π) (by simp [lexSites])

private def siteEnumFun (π : PatternData) (i : Fin (retainedSites π).card) :
    (retainedSites π : Finset Plane) := by
  let z := siteOrderIso π i
  have hmem : ofLex z.val ∈ retainedSites π := by
    rcases Finset.mem_map.mp z.property with ⟨x, hx, hzx⟩
    rw [← hzx]
    exact hx
  exact ⟨ofLex z.val, hmem⟩

private theorem siteEnumFun_lex (π : PatternData) (i : Fin (retainedSites π).card) :
    toLex (siteEnumFun π i).val = (siteOrderIso π i).val := by
  simp [siteEnumFun]

private def siteIndex (π : PatternData) (x : Plane) (hx : x ∈ retainedSites π) :
    Fin (retainedSites π).card :=
  (siteOrderIso π).symm ⟨toLex x, by simp [lexSites, hx]⟩

private theorem siteEnumFun_inj (π : PatternData) : Function.Injective (siteEnumFun π) := by
  intro i j hij
  apply (siteOrderIso π).injective
  apply Subtype.ext
  have hval := congrArg (fun s : (retainedSites π : Finset Plane) => toLex s.val) hij
  simpa [siteEnumFun] using hval

private theorem siteEnumFun_surj (π : PatternData) : Function.Surjective (siteEnumFun π) := by
  intro x
  let z : lexSites π := ⟨toLex x.val, by simp [lexSites, x.property]⟩
  refine ⟨(siteOrderIso π).symm z, ?_⟩
  apply Subtype.ext
  change ofLex (siteOrderIso π ((siteOrderIso π).symm z)).val = x.val
  simp [z]

private def siteEnum (π : PatternData) : Fin (retainedSites π).card ≃ (retainedSites π : Finset Plane) :=
  Equiv.ofBijective (siteEnumFun π) ⟨siteEnumFun_inj π, siteEnumFun_surj π⟩

private theorem siteEnumFun_siteIndex (π : PatternData) (x : retainedSites π) :
    siteEnumFun π (siteIndex π x.val x.property) = x := by
  apply Subtype.ext
  change ofLex (siteOrderIso π ((siteOrderIso π).symm
    ⟨toLex x.val, by simp [lexSites, x.property]⟩)).val = x.val
  simp

private theorem siteEnum_symm_eq_siteIndex (π : PatternData) (x : retainedSites π) :
    (siteEnum π).symm x = siteIndex π x.val x.property := by
  apply (siteEnum π).injective
  rw [(siteEnum π).apply_symm_apply]
  exact (siteEnumFun_siteIndex π x).symm

private theorem siteIndex_strict (π : PatternData) {x y : Plane}
    (hx : x ∈ retainedSites π) (hy : y ∈ retainedSites π)
    (hxy : toLex x < toLex y) : siteIndex π x hx < siteIndex π y hy := by
  unfold siteIndex
  apply (siteOrderIso π).symm.strictMono
  exact hxy

private theorem siteIndex_injective (π : PatternData) {x y : Plane}
    (hx : x ∈ retainedSites π) (hy : y ∈ retainedSites π)
    (hxy : siteIndex π x hx = siteIndex π y hy) : x = y := by
  have heq := congrArg (siteOrderIso π) hxy
  have hv : toLex x = toLex y := by
    simpa [siteIndex] using congrArg Subtype.val heq
  exact toLex.injective hv

private theorem siteIndex_eq_of_eq (π : PatternData) {x y : Plane}
    (hx : x ∈ retainedSites π) (hy : y ∈ retainedSites π) (hxy : x = y) :
    siteIndex π x hx = siteIndex π y hy := by
  subst y
  have hproof : hx = hy := Subsingleton.elim _ _
  subst hy
  rfl

private theorem siteIndex_enum (π : PatternData) (i : Fin (retainedSites π).card) :
    siteIndex π (siteEnum π i).val (siteEnum π i).property = i := by
  unfold siteIndex
  have hz : (⟨toLex (siteEnum π i).val, by simp [lexSites, (siteEnum π i).property]⟩ :
      lexSites π) = siteOrderIso π i := by
    apply Subtype.ext
    change toLex (siteEnumFun π i).val = (siteOrderIso π i).val
    exact siteEnumFun_lex π i
  rw [hz]
  exact (siteOrderIso π).symm_apply_apply i

private def retainedBonds (π : PatternData) : Finset (Plane × Plane) :=
  π.bonds.filter fun e => e.1 ≠ (0, 0) ∧ e.2 ≠ (0, 0)

private theorem bondEndpointsActive {π : PatternData} {e : Plane × Plane}
    (he : e ∈ π.bonds) : e.1 ∈ π.active ∧ e.2 ∈ π.active := by
  simp only [PatternData.bonds, Finset.mem_filter] at he
  rcases he with ⟨heB, hstatus⟩
  simp only [internalBonds, Finset.mem_biUnion] at heB
  rcases heB with ⟨x, hx, hxy⟩
  simp only [Finset.mem_image] at hxy
  rcases hxy with ⟨y, hy, hEq⟩
  have hyT : y ∈ templateSites := (Finset.mem_inter.mp hy).2
  have : e = (x, y) := hEq.symm
  subst e
  constructor <;> simp [PatternData.active, Finset.mem_filter, hx, hyT, hstatus]

private theorem retainedBondEndpoints {π : PatternData} {e : Plane × Plane}
    (he : e ∈ retainedBonds π) : e.1 ∈ retainedSites π ∧ e.2 ∈ retainedSites π := by
  simp only [retainedBonds, Finset.mem_filter] at he
  rcases he with ⟨he, hne⟩
  have hactive := bondEndpointsActive he
  simp [retainedSites, Finset.mem_erase, hactive, hne]

private theorem bondLexLt {π : PatternData} {e : Plane × Plane}
    (he : e ∈ π.bonds) : toLex e.1 < toLex e.2 := by
  simp only [PatternData.bonds, Finset.mem_filter] at he
  rcases he with ⟨heB, hstatus⟩
  simp only [internalBonds, Finset.mem_biUnion] at heB
  rcases heB with ⟨x, hx, hxy⟩
  simp only [Finset.mem_image] at hxy
  rcases hxy with ⟨y, hy, hEq⟩
  have hyPos := (Finset.mem_inter.mp hy).1
  have : e = (x, y) := hEq.symm
  subst e
  simp only [positiveNeighbours, Finset.mem_insert, Finset.mem_singleton] at hyPos
  rcases hyPos with hyPos | hyPos
  · subst y
    exact Prod.Lex.left _ _ (by omega)
  · subst y
    exact Prod.Lex.right _ (by omega)

private def mappedBond (π : PatternData) (e : {e : Plane × Plane // e ∈ retainedBonds π}) :
    Fin (retainedSites π).card × Fin (retainedSites π).card :=
  (siteIndex π e.1.1 (retainedBondEndpoints e.2).1,
   siteIndex π e.1.2 (retainedBondEndpoints e.2).2)

private theorem mappedBond_inj (π : PatternData) : Function.Injective (mappedBond π) := by
  intro a b hab
  apply Subtype.ext
  apply Prod.ext
  · apply siteIndex_injective π (retainedBondEndpoints a.2).1 (retainedBondEndpoints b.2).1
    exact congrArg Prod.fst hab
  · apply siteIndex_injective π (retainedBondEndpoints a.2).2 (retainedBondEndpoints b.2).2
    exact congrArg Prod.snd hab

private theorem mappedBond_incident_iff (π : PatternData)
    (i : Fin (retainedSites π).card) (a : {e : Plane × Plane // e ∈ retainedBonds π}) :
    (mappedBond π a).1 = i ∨ (mappedBond π a).2 = i ↔
      a.1.1 = (siteEnum π i).val ∨ a.1.2 = (siteEnum π i).val := by
  let x := (siteEnum π i).val
  have hx : x ∈ retainedSites π := (siteEnum π i).property
  have hi : siteIndex π x hx = i := siteIndex_enum π i
  constructor
  · intro h
    rcases h with h | h
    · left
      exact siteIndex_injective π (retainedBondEndpoints a.2).1 hx (h.trans hi.symm)
    · right
      exact siteIndex_injective π (retainedBondEndpoints a.2).2 hx (h.trans hi.symm)
  · intro h
    rcases h with h | h
    · left
      exact (siteIndex_eq_of_eq π (retainedBondEndpoints a.2).1 hx h).trans hi
    · right
      exact (siteIndex_eq_of_eq π (retainedBondEndpoints a.2).2 hx h).trans hi

private def slotsAt (x : Plane) : Finset (Fin 20) :=
  Finset.univ.filter fun j => (externalSlot j).1 = x

private def templateEdgesAt (x : Plane) : Finset (Plane × Plane) :=
  (internalBonds templateSites).filter fun e => e.1 = x ∨ e.2 = x

private theorem sourceDegree_le_template (π : PatternData)
    (i : Fin (retainedSites π).card) :
    ((retainedBonds π).attach.filter fun a =>
      a.1.1 = (siteEnum π i).val ∨ a.1.2 = (siteEnum π i).val).card ≤
      (templateEdgesAt (siteEnum π i).val).card := by
  let x := (siteEnum π i).val
  let S := (retainedBonds π).attach.filter fun a => a.1.1 = x ∨ a.1.2 = x
  refine Finset.card_le_card_of_injOn (s := S) (t := templateEdgesAt x)
    (fun a : {e : Plane × Plane // e ∈ retainedBonds π} => a.val) ?_ ?_
  · intro a ha
    have hpi : a.val ∈ π.bonds := (Finset.mem_filter.mp a.property).1
    have hint : a.val ∈ internalBonds templateSites := (Finset.mem_filter.mp hpi).1
    have hinc : a.val.1 = x ∨ a.val.2 = x := (Finset.mem_filter.mp ha).2
    simp [templateEdgesAt, hint, hinc]
  · intro a ha b hb hab
    apply Subtype.ext
    exact hab

private theorem templateDegreeSlotBound (x : Plane) (hx : x ∈ templateSites) :
    (templateEdgesAt x).card + (slotsAt x).card ≤ 4 := by
  simp [templateSites, square] at hx
  rcases x with ⟨a, b⟩
  change ((-2 ≤ a ∧ a ≤ 2) ∧ -2 ≤ b ∧ b ≤ 2) ∧ latticeDist (a, b) (0, 0) ≤ 2 at hx
  have ha₁ : -2 ≤ a := by omega
  have ha₂ : a ≤ 2 := by omega
  have hb₁ : -2 ≤ b := by omega
  have hb₂ : b ≤ 2 := by omega
  interval_cases a <;> interval_cases b <;>
    norm_num [templateSites, square, latticeDist] at hx <;>
    decide

private def slotEnum (x : Plane) : Fin (slotsAt x).card ≃ (slotsAt x : Finset (Fin 20)) :=
  (Finset.equivFin (slotsAt x)).symm

private def passageNetwork (π : PatternData) (m : Fin 20 → UnitVector) :
    FiniteSpinNetwork (retainedSites π).card := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun i => π.statusAt ((siteEnum π i).val)
  · exact (retainedBonds π).attach.image (mappedBond π)
  · exact fun i => (slotsAt ((siteEnum π i).val)).card
  · intro i j
    exact m ((slotEnum ((siteEnum π i).val) j).val)

private theorem passageNetwork_valid (π : PatternData) (m : Fin 20 → UnitVector) :
    (passageNetwork π m).Valid := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro i
    let x := (siteEnum π i).val
    have hxRet : x ∈ retainedSites π := (siteEnum π i).property
    have hxActive : x ∈ π.active := (Finset.mem_erase.mp hxRet).2
    have hnotX : π.statusAt x ≠ .X := (Finset.mem_filter.mp hxActive).2
    change π.statusAt x = .U ∨ π.statusAt x = .D
    cases hs : π.statusAt x <;> simp_all
  · intro e he
    rcases Finset.mem_image.mp he with ⟨a, ha, rfl⟩
    have hπ : a.val ∈ π.bonds := (Finset.mem_filter.mp a.property).1
    exact siteIndex_strict π (retainedBondEndpoints a.property).1
      (retainedBondEndpoints a.property).2 (bondLexLt hπ)
  · intro i
    let x := (siteEnum π i).val
    let S := (retainedBonds π).attach.filter fun a => a.1.1 = x ∨ a.1.2 = x
    have hxRet : x ∈ retainedSites π := (siteEnum π i).property
    have hxActive : x ∈ π.active := (Finset.mem_erase.mp hxRet).2
    have hxTemplate : x ∈ templateSites := (Finset.mem_filter.mp hxActive).1
    have hfilter : (passageNetwork π m).bonds.filter
        (fun e => e.1 = i ∨ e.2 = i) = S.image (mappedBond π) := by
      change Finset.filter (fun e => e.1 = i ∨ e.2 = i)
        ((retainedBonds π).attach.image (mappedBond π)) = S.image (mappedBond π)
      rw [Finset.filter_image]
      congr 1
      ext a
      simp only [S, Finset.mem_filter, Finset.mem_attach, true_and]
      change (mappedBond π a).1 = i ∨ (mappedBond π a).2 = i ↔
        a.val.1 = x ∨ a.val.2 = x
      exact mappedBond_incident_iff π i a
    have hinj : Set.InjOn (mappedBond π) (S : Set _) := by
      intro a ha b hb hab
      exact mappedBond_inj π hab
    have hcard : ((passageNetwork π m).bonds.filter
        (fun e => e.1 = i ∨ e.2 = i)).card = S.card := by
      rw [hfilter, Finset.card_image_of_injOn hinj]
    have hdegree : ((passageNetwork π m).bonds.filter
        (fun e => e.1 = i ∨ e.2 = i)).card ≤ (templateEdgesAt x).card := by
      rw [hcard]
      simpa [S, x] using sourceDegree_le_template π i
    have hgeometry := templateDegreeSlotBound x hxTemplate
    change ((passageNetwork π m).bonds.filter
      (fun e => e.1 = i ∨ e.2 = i)).card +
        (slotsAt x).card ≤ 4
    omega

private def sourceTerm (π : PatternData) (m : Fin 20 → UnitVector)
    (n : retainedSites π → SpinLetter) : ℝ :=
  (∏ x ∈ (retainedSites π).attach, spinWeight (π.statusAt x.val) (n x)) *
  (∏ e ∈ π.bonds, if e.1 = (0, 0) ∨ e.2 = (0, 0) then 1 else
    1 + dot (supportSpins (retainedSites π) n e.1) (supportSpins (retainedSites π) n e.2)) *
  ∏ j : Fin 20, if π.statusAt (externalSlot j).1 = .X then 1 else
    1 + dot (m j).val (supportSpins (retainedSites π) n (externalSlot j).1)

private def assignmentEquiv (π : PatternData) :
    (Fin (retainedSites π).card → SpinLetter) ≃ (retainedSites π → SpinLetter) :=
  Equiv.arrowCongr (siteEnum π) (Equiv.refl SpinLetter)

private theorem assignmentEquiv_apply (π : PatternData)
    (σ : Fin (retainedSites π).card → SpinLetter) (x : retainedSites π) :
    assignmentEquiv π σ x = σ (siteIndex π x.val x.property) := by
  simp [assignmentEquiv, siteEnum_symm_eq_siteIndex]

private def slotEqEquiv (π : PatternData) (x : retainedSites π) :
    {j : Fin 20 // j ∈ slotsAt x.val} ≃ {j : Fin 20 // (externalSlot j).1 = x.val} := by
  refine Equiv.mk (fun j => ⟨j.val, (Finset.mem_filter.mp j.property).2⟩)
    (fun j => ⟨j.val, by simp [slotsAt, j.property]⟩) ?_ ?_
  · intro j
    apply Subtype.ext
    rfl
  · intro j
    apply Subtype.ext
    rfl

private abbrev SlotIndex (π : PatternData) (x : retainedSites π) :=
  {j : Fin 20 // j ∈ slotsAt x.val}

private abbrev ActiveSlotIndex (π : PatternData) :=
  {j : Fin 20 // (externalSlot j).1 ∈ retainedSites π}

private def slotPairEquiv (π : PatternData) :
    (Σ x : retainedSites π, SlotIndex π x) ≃ ActiveSlotIndex π :=
  (Equiv.sigmaCongrRight (fun x => slotEqEquiv π x)).trans
    (Equiv.sigmaSubtypeFiberEquivSubtype
      (fun j : Fin 20 => (externalSlot j).1)
      (p := fun j => (externalSlot j).1 ∈ retainedSites π)
      (q := fun x => x ∈ retainedSites π)
      (fun _ => Iff.rfl))

private theorem slotPairEquiv_val (π : PatternData)
    (p : Σ x : retainedSites π, SlotIndex π x) :
    (slotPairEquiv π p).val = p.2.val := by
  simp [slotPairEquiv, slotEqEquiv, Equiv.sigmaSubtypeFiberEquivSubtype,
    Equiv.sigmaFiberEquiv,
    Equiv.subtypeSubtypeEquivSubtypeExists, Equiv.subtypeEquivRight]
  change (Equiv.refl (Fin 20)).symm p.2.val = p.2.val
  rfl

private theorem slotPairEquiv_site (π : PatternData)
    (p : Σ x : retainedSites π, SlotIndex π x) :
    (externalSlot (slotPairEquiv π p).val).1 = p.1.val := by
  rw [slotPairEquiv_val]
  exact (Finset.mem_filter.mp p.2.property).2

private def activeSlotSet (π : PatternData) : Finset (Fin 20) :=
  Finset.univ.filter fun j => (externalSlot j).1 ∈ retainedSites π

private def activeSlotEquiv (π : PatternData) :
    (activeSlotSet π : Finset (Fin 20)) ≃ ActiveSlotIndex π := by
  refine Equiv.mk (fun j => ⟨j.val, (Finset.mem_filter.mp j.property).2⟩)
    (fun j => ⟨j.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.property⟩⟩) ?_ ?_
  · intro j
    apply Subtype.ext
    rfl
  · intro j
    apply Subtype.ext
    rfl

private theorem slotSite_mem_template (j : Fin 20) :
    (externalSlot j).1 ∈ templateSites := by
  fin_cases j <;> decide

private theorem sourceSlots_eq_active (π : PatternData) (m : Fin 20 → UnitVector)
    (n : retainedSites π → SpinLetter) :
    (∏ j : Fin 20, if π.statusAt (externalSlot j).1 = .X then 1 else
      1 + dot (m j).val (supportSpins (retainedSites π) n (externalSlot j).1)) =
    (∏ j : Fin 20, if (externalSlot j).1 ∈ retainedSites π then
      1 + dot (m j).val (supportSpins (retainedSites π) n (externalSlot j).1) else 1) := by
  classical
  apply Fintype.prod_congr
  intro j
  let x := (externalSlot j).1
  change (if π.statusAt x = .X then 1 else
    1 + dot (m j).val (supportSpins (retainedSites π) n x)) =
    if x ∈ retainedSites π then
      1 + dot (m j).val (supportSpins (retainedSites π) n x) else 1
  by_cases hV : x ∈ retainedSites π
  · have hactive : x ∈ π.active := (Finset.mem_erase.mp hV).2
    have hnotX : π.statusAt x ≠ .X := (Finset.mem_filter.mp hactive).2
    simp [x, hV, hnotX]
  · by_cases hX : π.statusAt x = .X
    · simp [x, hV, hX]
    · have hxTemplate : x ∈ templateSites := slotSite_mem_template j
      have hactive : x ∈ π.active := by
        simp [PatternData.active, hxTemplate, hX]
      have hxOrigin : x = (0, 0) := by
        by_contra hxne
        have hret : x ∈ retainedSites π := by simp [retainedSites, hactive, hxne]
        exact hV hret
      have hV' : (0, 0) ∉ retainedSites π := by simpa [hxOrigin] using hV
      have hX' : π.statusAt (0, 0) ≠ .X := by simpa [hxOrigin] using hX
      simp [hxOrigin, hV', hX', supportSpins, dot]

private def targetPinFactor (π : PatternData) (m : Fin 20 → UnitVector)
    (σ : Fin (retainedSites π).card → SpinLetter) (i : Fin (retainedSites π).card)
    (k : Fin (slotsAt ((siteEnum π i).val)).card) : ℝ :=
  1 + dot ((passageNetwork π m).pin i k).val (spinVector (σ i))

private def sitePinFactor (π : PatternData) (m : Fin 20 → UnitVector)
    (σ : Fin (retainedSites π).card → SpinLetter) (x : retainedSites π)
    (k : Fin (slotsAt x.val).card) : ℝ :=
  1 + dot (m (slotEnum x.val k).val)
    (spinVector (assignmentEquiv π σ x))

private def sitePinProduct (π : PatternData) (m : Fin 20 → UnitVector)
    (σ : Fin (retainedSites π).card → SpinLetter) (x : retainedSites π) : ℝ :=
  Finset.univ.prod (fun (j : SlotIndex π x) =>
    1 + dot (m j.val).val (spinVector (assignmentEquiv π σ x)))

private def pairPinFactor (π : PatternData) (m : Fin 20 → UnitVector)
    (σ : Fin (retainedSites π).card → SpinLetter)
    (p : Σ x : retainedSites π, SlotIndex π x) : ℝ :=
  1 + dot (m p.2.val).val (spinVector (assignmentEquiv π σ p.1))

private def globalPinFactor (π : PatternData) (m : Fin 20 → UnitVector)
    (σ : Fin (retainedSites π).card → SpinLetter)
    (j : ActiveSlotIndex π) : ℝ :=
  1 + dot (m j.val).val
    (spinVector (assignmentEquiv π σ ⟨(externalSlot j.val).1, j.property⟩))

private theorem targetPins_eq_globalActive (π : PatternData) (m : Fin 20 → UnitVector)
    (σ : Fin (retainedSites π).card → SpinLetter) :
    (∏ i : Fin (retainedSites π).card,
      ∏ k : Fin (slotsAt ((siteEnum π i).val)).card, targetPinFactor π m σ i k) =
    (∏ j : ActiveSlotIndex π, globalPinFactor π m σ j) := by
  classical
  calc
    (∏ i : Fin (retainedSites π).card,
      ∏ k : Fin (slotsAt ((siteEnum π i).val)).card, targetPinFactor π m σ i k) =
      ∏ x : retainedSites π, ∏ k : Fin (slotsAt x.val).card, sitePinFactor π m σ x k := by
        apply Fintype.prod_equiv (siteEnum π)
        intro i
        simp [targetPinFactor, sitePinFactor, passageNetwork, assignmentEquiv_apply,
          siteIndex_enum]
    _ = ∏ x : retainedSites π, sitePinProduct π m σ x := by
        apply Fintype.prod_congr
        intro x
        unfold sitePinProduct
        apply Fintype.prod_equiv (slotEnum x.val)
        intro k
        simp [sitePinFactor, slotEnum]
    _ = ∏ p : Σ x : retainedSites π, SlotIndex π x, pairPinFactor π m σ p := by
        symm
        exact Fintype.prod_sigma (pairPinFactor π m σ)
    _ = ∏ j : ActiveSlotIndex π,
        globalPinFactor π m σ j := by
        apply Fintype.prod_equiv (slotPairEquiv π)
        intro p
        change 1 + dot (m p.2.val).val
          (spinVector (assignmentEquiv π σ p.1)) =
          1 + dot (m (slotPairEquiv π p).val).val
            (spinVector (assignmentEquiv π σ
              ⟨(externalSlot (slotPairEquiv π p).val).1, (slotPairEquiv π p).property⟩))
        have hx : (⟨(externalSlot (slotPairEquiv π p).val).1,
            (slotPairEquiv π p).property⟩ : retainedSites π) = p.1 :=
          Subtype.ext (slotPairEquiv_site π p)
        have hspin : spinVector (assignmentEquiv π σ
            ⟨(externalSlot (slotPairEquiv π p).val).1,
              (slotPairEquiv π p).property⟩) =
            spinVector (assignmentEquiv π σ p.1) :=
          congrArg spinVector (congrArg (assignmentEquiv π σ) hx)
        calc
          1 + dot (m p.2.val).val (spinVector (assignmentEquiv π σ p.1)) =
              1 + dot (m (slotPairEquiv π p).val).val
                (spinVector (assignmentEquiv π σ p.1)) := by
                  rw [slotPairEquiv_val π p]
          _ = 1 + dot (m (slotPairEquiv π p).val).val
                (spinVector (assignmentEquiv π σ
                  ⟨(externalSlot (slotPairEquiv π p).val).1,
                    (slotPairEquiv π p).property⟩)) := by rw [← hspin]

private theorem withoutPassage_eq_sourceSum (π : PatternData) (m : Fin 20 → UnitVector) :
    withoutPassageFunctional π m (fun _ => 1) =
      ∑ n : retainedSites π → SpinLetter, sourceTerm π m n := by
  classical
  unfold AKLT.Defs.withoutPassageFunctional
  simp only [sourceTerm, retainedSites, Finset.univ_eq_attach]
  apply Fintype.sum_congr
  intro n
  ring_nf

private theorem passagePartition_eq_targetSum (π : PatternData) (m : Fin 20 → UnitVector) :
    (passageNetwork π m).partition true (fun _ => 1) =
      ∑ σ : Fin (retainedSites π).card → SpinLetter,
        (passageNetwork π m).weight true σ := by
  simp [FiniteSpinNetwork.partition, FiniteSpinNetwork.weight]

private theorem siteWeights_eq (π : PatternData)
    (σ : Fin (retainedSites π).card → SpinLetter) :
    (∏ i : Fin (retainedSites π).card,
      spinWeight (π.statusAt (siteEnum π i).val) (σ i)) =
      (∏ x ∈ (retainedSites π).attach,
        spinWeight (π.statusAt x.val) (assignmentEquiv π σ x)) := by
  classical
  have h := Fintype.prod_equiv (siteEnum π)
    (fun i => spinWeight (π.statusAt (siteEnum π i).val) (σ i))
    (fun x => spinWeight (π.statusAt x.val) (assignmentEquiv π σ x))
    (by
      intro i
      rw [assignmentEquiv_apply, siteIndex_enum])
  simpa only [Finset.univ_eq_attach] using h

private theorem sourceBonds_eq_retained (π : PatternData) (_m : Fin 20 → UnitVector)
    (n : retainedSites π → SpinLetter) :
    (∏ e ∈ π.bonds, if e.1 = (0, 0) ∨ e.2 = (0, 0) then 1 else
      1 + dot (supportSpins (retainedSites π) n e.1) (supportSpins (retainedSites π) n e.2)) =
    Finset.prod (retainedBonds π : Finset (Plane × Plane)) (fun (e : Plane × Plane) =>
      1 + dot (supportSpins (retainedSites π) n e.1)
        (supportSpins (retainedSites π) n e.2)) := by
  classical
  let p : Plane × Plane → Prop := fun (e : Plane × Plane) => e.1 ≠ (0, 0) ∧ e.2 ≠ (0, 0)
  let f : Plane × Plane → ℝ := fun (e : Plane × Plane) =>
    1 + dot (supportSpins (retainedSites π) n e.1)
      (supportSpins (retainedSites π) n e.2)
  calc
    (∏ e ∈ π.bonds, if e.1 = (0, 0) ∨ e.2 = (0, 0) then 1 else f e) =
        ∏ e ∈ π.bonds, if p e then f e else 1 := by
      apply Finset.prod_congr rfl
      intro e he
      by_cases h : e.1 = (0, 0) ∨ e.2 = (0, 0)
      · have hp : ¬ p e := by
          intro hp
          rcases h with h | h
          · exact hp.1 h
          · exact hp.2 h
        simp [h, hp, f]
      · have hp : p e := by
          constructor
          · intro h₁
            exact h (Or.inl h₁)
          · intro h₂
            exact h (Or.inr h₂)
        simp [h, hp, f]
    _ = ∏ e ∈ π.bonds with p e, f e := by
      symm
      exact Finset.prod_filter p f
    _ = Finset.prod (retainedBonds π : Finset (Plane × Plane)) f := by
      simp [retainedBonds, p, f]

private theorem targetBonds_eq_source (π : PatternData) (m : Fin 20 → UnitVector)
    (σ : Fin (retainedSites π).card → SpinLetter) :
    Finset.prod ((passageNetwork π m).bonds : Finset
      (Fin (retainedSites π).card × Fin (retainedSites π).card))
      (fun (e : Fin (retainedSites π).card × Fin (retainedSites π).card) =>
        1 + dot (spinVector (σ e.1)) (spinVector (σ e.2))) =
    Finset.prod (π.bonds : Finset (Plane × Plane)) (fun (e : Plane × Plane) =>
      if e.1 = (0, 0) ∨ e.2 = (0, 0) then 1 else
        1 + dot (supportSpins (retainedSites π) (assignmentEquiv π σ) e.1)
          (supportSpins (retainedSites π) (assignmentEquiv π σ) e.2)) := by
  classical
  let n := assignmentEquiv π σ
  let ef : Fin (retainedSites π).card × Fin (retainedSites π).card → ℝ := fun e =>
    1 + dot (spinVector (σ e.1)) (spinVector (σ e.2))
  let sf : Plane × Plane → ℝ := fun e =>
    1 + dot (supportSpins (retainedSites π) n e.1)
      (supportSpins (retainedSites π) n e.2)
  calc
    (∏ e ∈ (passageNetwork π m).bonds, ef e) =
        ∏ a ∈ (retainedBonds π).attach, sf a.val := by
      change (∏ e ∈ (retainedBonds π).attach.image (mappedBond π), ef e) = _
      rw [Finset.prod_image (fun a ha b hb hab => mappedBond_inj π hab)]
      apply Finset.prod_congr rfl
      intro a ha
      have hends := retainedBondEndpoints a.property
      simp [ef, sf, n, assignmentEquiv_apply, mappedBond, supportSpins, hends]
    _ = Finset.prod (retainedBonds π) sf := by
      rw [Finset.prod_attach]
    _ = (∏ e ∈ π.bonds, if e.1 = (0, 0) ∨ e.2 = (0, 0) then 1 else sf e) := by
      symm
      exact sourceBonds_eq_retained π m n

private theorem targetPins_eq_sourceSlots (π : PatternData) (m : Fin 20 → UnitVector)
    (σ : Fin (retainedSites π).card → SpinLetter) :
    (∏ i : Fin (retainedSites π).card,
      ∏ k : Fin (slotsAt ((siteEnum π i).val)).card, targetPinFactor π m σ i k) =
    (∏ j : Fin 20, if (externalSlot j).1 ∈ retainedSites π then
      1 + dot (m j).val
        (supportSpins (retainedSites π) (assignmentEquiv π σ) (externalSlot j).1) else 1) := by
  classical
  let g : Fin 20 → ℝ := fun j =>
    if h : (externalSlot j).1 ∈ retainedSites π then
      1 + dot (m j).val
        (spinVector (assignmentEquiv π σ ⟨(externalSlot j).1, h⟩))
    else 1
  calc
    _ = ∏ j : ActiveSlotIndex π, globalPinFactor π m σ j :=
      targetPins_eq_globalActive π m σ
    _ = ∏ j : activeSlotSet π, g j.val := by
      apply Fintype.prod_equiv (activeSlotEquiv π).symm
      intro j
      simp [g, globalPinFactor, activeSlotEquiv, j.property]
    _ = ∏ j ∈ activeSlotSet π, g j := by
      simp only [Finset.univ_eq_attach]
      rw [Finset.prod_attach]
    _ = ∏ j ∈ Finset.univ with j ∈ activeSlotSet π, g j := by
      simp [activeSlotSet]
    _ = ∏ j : Fin 20, if j ∈ activeSlotSet π then g j else 1 := by
      exact Finset.prod_filter _ _
    _ = ∏ j : Fin 20, if (externalSlot j).1 ∈ retainedSites π then
        1 + dot (m j).val
          (supportSpins (retainedSites π) (assignmentEquiv π σ) (externalSlot j).1) else 1 := by
      apply Fintype.prod_congr
      intro j
      by_cases h : (externalSlot j).1 ∈ retainedSites π
      · simp [activeSlotSet, g, h, supportSpins]
      · simp [activeSlotSet, g, h]

private theorem targetWeight_eq_sourceTerm (π : PatternData) (m : Fin 20 → UnitVector)
    (σ : Fin (retainedSites π).card → SpinLetter) :
    (passageNetwork π m).weight true σ =
      sourceTerm π m (assignmentEquiv π σ) := by
  classical
  rw [FiniteSpinNetwork.weight, sourceTerm]
  change
    ((∏ i : Fin (retainedSites π).card,
        spinWeight (π.statusAt (siteEnum π i).val) (σ i)) *
      Finset.prod ((passageNetwork π m).bonds)
        (fun e => 1 + dot (spinVector (σ e.1)) (spinVector (σ e.2)))) *
      (∏ i : Fin (retainedSites π).card,
        ∏ k : Fin (slotsAt ((siteEnum π i).val)).card,
          targetPinFactor π m σ i k) = _
  rw [siteWeights_eq π σ]
  rw [targetBonds_eq_source π m σ]
  rw [targetPins_eq_sourceSlots π m σ]
  rw [sourceSlots_eq_active π m (assignmentEquiv π σ)]

private theorem passagePartition_eq_withoutPassage (π : PatternData)
    (m : Fin 20 → UnitVector) :
    (passageNetwork π m).partition true (fun _ => 1) =
      withoutPassageFunctional π m (fun _ => 1) := by
  classical
  rw [passagePartition_eq_targetSum]
  rw [withoutPassage_eq_sourceSum]
  calc
    (∑ σ : Fin (retainedSites π).card → SpinLetter,
      (passageNetwork π m).weight true σ) =
        ∑ σ : Fin (retainedSites π).card → SpinLetter,
          sourceTerm π m (assignmentEquiv π σ) := by
      apply Fintype.sum_congr
      intro σ
      exact targetWeight_eq_sourceTerm π m σ
    _ = ∑ n : retainedSites π → SpinLetter, sourceTerm π m n := by
      exact Fintype.sum_equiv (assignmentEquiv π) _ _ (fun _ => rfl)

theorem main : AKLT.Blueprint.H1.PassageNetworkPositiveStatement := by
  intro hfinite π _hcovered m
  have hvalid := passageNetwork_valid π m
  have hpositive := hfinite (retainedSites π).card (passageNetwork π m) hvalid
  rw [passagePartition_eq_withoutPassage π m] at hpositive
  exact hpositive

end AKLT.W.H1M007

#print axioms AKLT.W.H1M007.main
