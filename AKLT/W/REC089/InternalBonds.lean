module
public import AKLT.W.REC089.CutBonds
public import AKLT.W.REC089.PatternFactorization

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC089

attribute [local instance] Classical.propDecidable

theorem pattern_oriented_iff (π : PatternData) {e : Plane × Plane}
    (he : e ∈ internalBonds templateSites) :
    e ∈ π.bonds ↔ π.InternalPresent e.1 e.2 := by
  have hp := (AKLT.W.REC003.mem_internal _ _).mp he |>.2.1
  have hn : (e.2, e.1) ∉ π.bonds := by
    intro h
    exact AKLT.W.REC003.positive_asymm hp
      ((AKLT.W.REC003.mem_internal _ _).mp (Finset.mem_filter.mp h).1).2.1
  simp [PatternData.InternalPresent, hn]

theorem actual_tip_oriented (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass) (t : Fin 4) :
    actualTipBond a incoming t = true ↔
      a.D.Present (localChart a incoming (tipEdge t).1)
        (localChart a incoming (tipEdge t).2) := by
  unfold actualTipBond
  rw [decide_eq_true_eq]
  rcases tipEdge_endpoints t with h | h
  · rw [h]
  · rw [h]
    exact ⟨AKLT.W.REC003.present_symm, AKLT.W.REC003.present_symm⟩

theorem inside_bonds_split (a : AKLT.Blueprint.Rec.Departure) (incoming outgoing : Compass)
    (π : PatternData) (hm : Matches a incoming outgoing π) :
    insideBonds a incoming = coreBonds π ∪
      ((Finset.univ.filter fun t => actualTipBond a incoming t = true).image tipEdge) := by
  ext e
  constructor
  · intro he
    obtain ⟨he, hp⟩ := Finset.mem_filter.mp he
    by_cases hc : e.1 ∉ templateTips ∧ e.2 ∉ templateTips
    · apply Finset.mem_union_left
      have hs := (AKLT.W.REC003.mem_internal _ _).mp he
      have hmatch := hm.2.2.2 e.1 (Finset.mem_sdiff.mpr ⟨hs.1, hc.1⟩) e.2 hs.2.2
      rw [ite_eq_right hc.2] at hmatch
      exact Finset.mem_filter.mpr ⟨(pattern_oriented_iff π he).mpr (hmatch.mpr hp), hc⟩
    · obtain ⟨t, rfl⟩ := internal_tip_classification ⟨e, he⟩ (by tauto)
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (actual_tip_oriented a incoming t).mpr hp⟩, rfl⟩)
  · intro he
    rcases Finset.mem_union.mp he with hc | ht
    · obtain ⟨hb, hn⟩ := Finset.mem_filter.mp hc
      have hi := (Finset.mem_filter.mp hb).1
      have hs := (AKLT.W.REC003.mem_internal _ _).mp hi
      have hmatch := hm.2.2.2 e.1 (Finset.mem_sdiff.mpr ⟨hs.1, hn.1⟩) e.2 hs.2.2
      rw [ite_eq_right hn.2] at hmatch
      exact Finset.mem_filter.mpr ⟨hi, hmatch.mp ((pattern_oriented_iff π hi).mp hb)⟩
    · obtain ⟨t, hmem, rfl⟩ := Finset.mem_image.mp ht
      exact Finset.mem_filter.mpr ⟨tipEdge_internal t,
        (actual_tip_oriented a incoming t).mp (Finset.mem_filter.mp hmem).2⟩

theorem inside_bonds_disjoint (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass)
    (π : PatternData) :
    Disjoint (coreBonds π)
      ((Finset.univ.filter fun t => actualTipBond a incoming t = true).image tipEdge) := by
  apply Finset.disjoint_left.mpr
  intro e he ht
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp ht
  exact tipEdge_not_core t (Finset.mem_filter.mp he).2

theorem networkBondTerm_canonical (a : AKLT.Blueprint.Rec.Departure) (incoming outgoing : Compass)
    (ho : a.o = a.y + outgoing.step) (π : PatternData) (hm : Matches a incoming outgoing π)
    (next : Bool) (v : Plane → Vec3) (e : Plane × Plane) :
    networkBondTerm a next v (chartEdge a incoming e) =
      templateBondTerm π next (fun z => v (localChart a incoming z)) e := by
  rw [networkBondTerm_chart]
  unfold networkBondTerm templateBondTerm
  simp only [network_drop_local a incoming outgoing ho π hm]

theorem inside_bond_product (a : AKLT.Blueprint.Rec.Departure) (incoming outgoing : Compass)
    (ho : a.o = a.y + outgoing.step) (π : PatternData) (hm : Matches a incoming outgoing π)
    (next : Bool) (v : Plane → Vec3) :
    (∏ e ∈ insideBonds a incoming, networkBondTerm a next v (chartEdge a incoming e)) =
      (∏ e ∈ coreBonds π,
        templateBondTerm π next (fun z => v (localChart a incoming z)) e) *
      ∏ t : Fin 4, if actualTipBond a incoming t then
        1 + dot (v (localChart a incoming (tipPoint t)))
          (v (localChart a incoming (tipNeighbor t))) else 1 := by
  simp_rw [networkBondTerm_canonical a incoming outgoing ho π hm]
  conv_lhs => rw [inside_bonds_split a incoming outgoing π hm,
    Finset.prod_union (inside_bonds_disjoint a incoming π)]
  congr 1
  rw [Finset.prod_image (fun _ _ _ _ h => tipEdge_injective h), Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro t _
  by_cases h : actualTipBond a incoming t = true
  · simp only [h, ite_true, templateBondTerm, tipEdge_not_dropped, and_false, ite_false]
    rcases tipEdge_endpoints t with he | he <;> rw [he]
    rw [dot_comm]
  · simp [h]

#print axioms inside_bonds_split
#print axioms inside_bond_product

end AKLT.W.REC089
