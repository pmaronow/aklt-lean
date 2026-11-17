module
public import AKLT.W.REC089.FiniteSums
public import AKLT.W.REC096.Main
public import AKLT.W.REC003.Main

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC089

def tipEdge : Fin 4 → Plane × Plane :=
  ![((1, 0), (2, 0)), ((0, 1), (0, 2)), ((-2, 0), (-1, 0)), ((0, -2), (0, -1))]

theorem tipPoint_injective : Function.Injective tipPoint := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [tipPoint]

theorem tipEdge_injective : Function.Injective tipEdge := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [tipEdge]

theorem tipPoint_surjective : ∀ x ∈ templateTips, ∃ t, tipPoint t = x := by
  intro x hx
  simp only [templateTips, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

def tipEquiv : Fin 4 ≃ templateTips :=
  Equiv.ofBijective (fun t => ⟨tipPoint t, (tipPoint_mem t).2⟩) ⟨
    fun _ _ h => tipPoint_injective (congrArg Subtype.val h),
    fun x => by
      obtain ⟨t, ht⟩ := tipPoint_surjective x x.property
      exact ⟨t, Subtype.ext ht⟩⟩

@[simp] theorem tipEquiv_val (t : Fin 4) : (tipEquiv t).val = tipPoint t := rfl

theorem tipEdge_endpoints (t : Fin 4) :
    tipEdge t = (tipNeighbor t, tipPoint t) ∨
      tipEdge t = (tipPoint t, tipNeighbor t) := by
  fin_cases t <;> simp [tipEdge, tipNeighbor, tipPoint]

theorem tipEdge_internal (t : Fin 4) : tipEdge t ∈ internalBonds templateSites := by
  revert t
  decide +kernel

theorem tipEdge_not_core (t : Fin 4) :
    ¬((tipEdge t).1 ∉ templateTips ∧ (tipEdge t).2 ∉ templateTips) := by
  revert t
  decide +kernel

theorem internal_tip_classification :
    ∀ e : internalBonds templateSites,
      (e.val.1 ∈ templateTips ∨ e.val.2 ∈ templateTips) → ∃ t, e.val = tipEdge t := by
  decide +kernel

theorem coverTipBond_iff (π : PatternData) (t : Fin 4) :
    coverTipBond π t = true ↔ tipEdge t ∈ π.bonds := by
  classical
  have hnot : ((tipEdge t).2, (tipEdge t).1) ∉ internalBonds templateSites := by
    revert t
    decide +kernel
  have hn : ((tipEdge t).2, (tipEdge t).1) ∉ π.bonds :=
    fun h => hnot (Finset.mem_filter.mp h).1
  fin_cases t <;>
    simp_all [coverTipBond, PatternData.InternalPresent, tipNeighbor, tipPoint, tipEdge]

theorem pattern_bonds_split (π : PatternData) :
    π.bonds = coreBonds π ∪
      ((Finset.univ.filter fun t => coverTipBond π t = true).image tipEdge) := by
  classical
  ext e
  constructor
  · intro he
    by_cases hc : e.1 ∉ templateTips ∧ e.2 ∉ templateTips
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he, hc⟩)
    · have ht : e.1 ∈ templateTips ∨ e.2 ∈ templateTips := by tauto
      obtain ⟨t, rfl⟩ := internal_tip_classification
        ⟨e, (Finset.mem_filter.mp he).1⟩ ht
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (coverTipBond_iff π t).mpr he⟩, rfl⟩)
  · intro he
    rcases Finset.mem_union.mp he with hc | ht
    · exact (Finset.mem_filter.mp hc).1
    · obtain ⟨t, hmem, rfl⟩ := Finset.mem_image.mp ht
      exact (coverTipBond_iff π t).mp (Finset.mem_filter.mp hmem).2

theorem pattern_bonds_disjoint (π : PatternData) :
    Disjoint (coreBonds π)
      ((Finset.univ.filter fun t => coverTipBond π t = true).image tipEdge) := by
  classical
  apply Finset.disjoint_left.mpr
  intro e he ht
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp ht
  exact tipEdge_not_core t (Finset.mem_filter.mp he).2

theorem pattern_bond_active (π : PatternData) {e : Plane × Plane} (he : e ∈ π.bonds) :
    e.1 ∈ π.active ∧ e.2 ∈ π.active := by
  have h := Finset.mem_filter.mp he
  have hs := (AKLT.W.REC003.mem_internal _ _).mp h.1
  exact ⟨Finset.mem_filter.mpr ⟨hs.1, h.2.1⟩,
    Finset.mem_filter.mpr ⟨hs.2.2, h.2.2.1⟩⟩

theorem pattern_tip_active (π : PatternData) (hπ : π.Covered) (t : Fin 4) :
    tipPoint t ∈ π.active :=
  Finset.mem_filter.mpr ⟨(tipPoint_mem t).1, by
    rw [hπ.2.2.2.2.2.2.2.2.1 _ (tipPoint_mem t).2]
    decide⟩

def patternSiteEquiv (π : PatternData) (hπ : π.Covered) :
    π.active ≃ coreSites π ⊕ Fin 4 where
  toFun x := if h : x.val ∈ templateTips then
      .inr (tipEquiv.symm ⟨x.val, h⟩)
    else .inl ⟨x.val, Finset.mem_sdiff.mpr ⟨x.property, h⟩⟩
  invFun x := match x with
    | .inl c => ⟨c.val, (Finset.mem_sdiff.mp c.property).1⟩
    | .inr t => ⟨tipPoint t, pattern_tip_active π hπ t⟩
  left_inv x := by
    dsimp
    split_ifs with ht
    · apply Subtype.ext
      change tipPoint (tipEquiv.symm ⟨x.val, ht⟩) = x.val
      exact congrArg (fun z : templateTips => z.val)
        (tipEquiv.apply_symm_apply ⟨x.val, ht⟩)
    · rfl
  right_inv x := by
    cases x with
    | inl c =>
      dsimp
      rw [dite_eq_right (Finset.mem_sdiff.mp c.property).2]
    | inr t =>
      dsimp
      rw [dif_pos (tipPoint_mem t).2]
      congr 1
      exact tipEquiv.symm_apply_apply t

@[simp] theorem patternSiteEquiv_inl (π : PatternData) (hπ : π.Covered)
    (c : coreSites π) :
    ((patternSiteEquiv π hπ).symm (.inl c)).val = c.val := rfl

@[simp] theorem patternSiteEquiv_inr (π : PatternData) (hπ : π.Covered) (t : Fin 4) :
    ((patternSiteEquiv π hπ).symm (.inr t)).val = tipPoint t := rfl

theorem slot_index_equiv : Function.Bijective
    (Sum.elim cornerIndex (fun p : Fin 4 × Fin 3 => tipIndex p.1 p.2)) := by
  decide +kernel

def slotEquiv : (Fin 8 ⊕ (Fin 4 × Fin 3)) ≃ Fin 20 :=
  Equiv.ofBijective _ slot_index_equiv

theorem prod_slots (f : Fin 20 → ℝ) :
    (∏ j, f j) = (∏ j, f (cornerIndex j)) * ∏ t, ∏ j, f (tipIndex t j) := by
  rw [← slotEquiv.prod_comp, Fintype.prod_sum_type, Fintype.prod_prod_type]
  rfl

theorem tip_slot_site (t : Fin 4) (j : Fin 3) :
    (externalSlot (tipIndex t j)).1 = tipPoint t := by
  revert t j
  decide +kernel

theorem corner_slot_core (j : Fin 8) :
    (externalSlot (cornerIndex j)).1 ∈ templateSites \ templateTips := by
  revert j
  decide +kernel

theorem tip_not_center (t : Fin 4) : tipPoint t ≠ (0, 0) := by
  revert t
  decide +kernel

theorem tip_not_outgoing (t : Fin 4) (d : Compass) : tipPoint t ≠ d.step := by
  revert t d
  decide +kernel

theorem tipEdge_not_dropped (t : Fin 4) (d : Compass) :
    ({(tipEdge t).1, (tipEdge t).2} : Finset Plane) ≠ {(0, 0), d.step} := by
  revert t d
  decide +kernel

#print axioms pattern_bonds_split
#print axioms patternSiteEquiv

end AKLT.W.REC089
