module
public import AKLT.Blueprint.H1.NodesReduction

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.H1M023

private lemma template_bonds :
    ∀ e ∈ internalBonds templateSites,
      e.1 ∈ templateSites ∧ e.2 ∈ templateSites ∧ e.1 ≠ e.2 ∧
      ¬ (e.1 ∈ templateCorners ∪ templateTips ∧ e.2 ∈ templateCorners ∪ templateTips) := by
  decide +kernel

private lemma template_degrees :
    ∀ x ∈ templateSites,
      ((internalBonds templateSites).filter fun e => e.1 = x ∨ e.2 = x).card ≤
        if x ∈ templateCorners then 2 else 4 := by
  decide +kernel

private lemma template_tip_degrees :
    ∀ x ∈ templateTips,
      ((internalBonds templateSites).filter fun e => e.1 = x ∨ e.2 = x).card ≤ 1 := by
  decide +kernel

lemma bond_info (π : PatternData) {e : Plane × Plane} (he : e ∈ π.bonds) :
    e.1 ∈ π.active ∧ e.2 ∈ π.active ∧ e.1 ≠ e.2 ∧
      ¬ (e.1 ∈ templateCorners ∪ templateTips ∧ e.2 ∈ templateCorners ∪ templateTips) := by
  have ht := template_bonds e (Finset.mem_filter.mp he).1
  have hs := (Finset.mem_filter.mp he).2
  exact ⟨Finset.mem_filter.mpr ⟨ht.1, hs.1⟩,
    Finset.mem_filter.mpr ⟨ht.2.1, hs.2.1⟩, ht.2.2⟩

lemma pattern_degree_bound (π : PatternData) (x : Plane) :
    patternDegree π x ≤ if x ∈ templateCorners then 2 else 4 := by
  by_cases hx : x ∈ templateSites
  · exact (Finset.card_le_card (Finset.filter_subset_filter _
      (Finset.filter_subset _ _))).trans (template_degrees x hx)
  · have hzero : patternDegree π x = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      have hi := bond_info π (Finset.mem_filter.mp he).1
      rcases (Finset.mem_filter.mp he).2 with h | h
      · exact hx (h ▸ (Finset.mem_filter.mp hi.1).1)
      · exact hx (h ▸ (Finset.mem_filter.mp hi.2.1).1)
    rw [hzero]
    exact Nat.zero_le _

lemma pattern_tip_degree_bound (π : PatternData) {x : Plane} (hx : x ∈ templateTips) :
    patternDegree π x ≤ 1 := by
  exact (Finset.card_le_card (Finset.filter_subset_filter _
    (Finset.filter_subset _ _))).trans (template_tip_degrees x hx)

lemma positive_degree_active (π : PatternData) {x : Plane} (hx : 0 < patternDegree π x) :
    x ∈ π.active := by
  obtain ⟨e, he⟩ := Finset.card_pos.mp hx
  have hi := bond_info π (Finset.mem_filter.mp he).1
  rcases (Finset.mem_filter.mp he).2 with h | h
  · exact h ▸ hi.1
  · exact h ▸ hi.2.1

lemma group_pair_retained (π : PatternData) (r : Representation) {x : Plane}
    (hx : x ∈ reductionGroups π) (hp : groupIsPair π r x = true) :
    x ∈ reducedSpinSites π r := by
  classical
  have hpos := (Finset.mem_filter.mp hx).2
  have hc : x ∈ templateCorners ∧ ¬ SingleReplacement π r x := by
    simpa [groupIsPair] using hp
  exact Finset.mem_filter.mpr ⟨positive_degree_active π hpos,
    (fun ht => hc.2 ⟨by have := pattern_tip_degree_bound π ht; omega, Or.inl ht⟩),
    Or.inr ⟨Nat.ne_of_gt hpos, hc.2⟩⟩

lemma group_single (π : PatternData) (r : Representation) {x : Plane}
    (hx : x ∈ reductionGroups π) (hp : groupIsPair π r x = false) :
    SingleReplacement π r x ∧ x ∉ reducedSpinSites π r := by
  classical
  have hpos := (Finset.mem_filter.mp hx).2
  have hc : ¬ (x ∈ templateCorners ∧ ¬ SingleReplacement π r x) := by
    simpa [groupIsPair] using hp
  have hs : SingleReplacement π r x := by
    rcases Finset.mem_union.mp (Finset.mem_filter.mp hx).1 with hx | hx
    · exact Classical.not_not.mp (fun hn => hc ⟨hx, hn⟩)
    · exact ⟨by have := pattern_tip_degree_bound π hx; omega, Or.inl hx⟩
  refine ⟨hs, ?_⟩
  intro hv
  have hv := (Finset.mem_filter.mp hv).2
  rcases hs.2 with ht | ⟨hr, hc⟩
  · exact hv.1 ht
  · rcases hv.2 with hn | hn
    · exact hn hc
    · exact hn.2 hs

/-- The other endpoint of an incident bond. -/
def otherEnd (x : Plane) (e : Plane × Plane) : Plane := if e.1 = x then e.2 else e.1

lemma leaf_bond (π : PatternData) {x : Plane} (hx : patternDegree π x = 1) :
    ∃ e ∈ π.bonds, (e.1 = x ∨ e.2 = x) ∧
      leafNeighbor π x = otherEnd x e ∧
      ∀ f ∈ π.bonds, (f.1 = x ∨ f.2 = x) → f = e := by
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp hx
  have he' : e ∈ π.bonds ∧ (e.1 = x ∨ e.2 = x) := by
    exact Finset.mem_filter.mp (he.symm ▸ Finset.mem_singleton_self e)
  have hu : ∀ f ∈ π.bonds, (f.1 = x ∨ f.2 = x) → f = e := by
    intro f hf hfx
    have := he ▸ Finset.mem_filter.mpr ⟨hf, hfx⟩
    exact Finset.mem_singleton.mp this
  let L := π.bonds.toList.filterMap fun f =>
    if f.1 = x then some f.2 else if f.2 = x then some f.1 else none
  have hmem : otherEnd x e ∈ L := by
    apply List.mem_filterMap.mpr
    refine ⟨e, Finset.mem_toList.mpr he'.1, ?_⟩
    rcases he'.2 with h | h
    · simp [otherEnd, h]
    · by_cases h1 : e.1 = x <;> simp [otherEnd, h, h1]
  have hne : L ≠ [] := List.ne_nil_of_mem hmem
  have hhead : L.headD (0, 0) ∈ L := by
    cases hL : L with
    | nil => exact False.elim (hne hL)
    | cons a as => simp
  obtain ⟨f, hf, hfm⟩ := List.mem_filterMap.mp hhead
  have hfx : f.1 = x ∨ f.2 = x := by
    by_contra hn
    simp only [not_or] at hn
    simp [hn.1, hn.2] at hfm
  have hfe := hu f (Finset.mem_toList.mp hf) hfx
  subst f
  have hval : L.headD (0, 0) = otherEnd x e := by
    rcases he'.2 with h | h
    · simpa [h, otherEnd] using hfm.symm
    · by_cases h1 : e.1 = x <;> simpa [h, h1, otherEnd] using hfm.symm
  exact ⟨e, he'.1, he'.2, hval, hu⟩

lemma group_single_neighbor_retained (π : PatternData) (r : Representation) {x : Plane}
    (hx : x ∈ reductionGroups π) (hp : groupIsPair π r x = false) :
    leafNeighbor π x ∈ reducedSpinSites π r := by
  classical
  have hs := group_single π r hx hp
  obtain ⟨e, he, hei, hne, hu⟩ := leaf_bond π hs.1.1
  have hi := bond_info π he
  have hper := (Finset.mem_filter.mp hx).1
  rw [hne]
  have hn : otherEnd x e ∈ π.active ∧
      otherEnd x e ∉ templateCorners ∪ templateTips := by
    rcases hei with hei | hei
    · subst x
      simpa [otherEnd, hper] using
        And.intro hi.2.1 (fun h => hi.2.2.2 ⟨hper, h⟩)
    · have hneq : e.1 ≠ x := by simpa [hei] using hi.2.2.1
      simpa [otherEnd, hneq] using
        And.intro hi.1 (fun h => hi.2.2.2 ⟨h, hei ▸ hper⟩)
  exact Finset.mem_filter.mpr ⟨hn.1, (fun h => hn.2 (Finset.mem_union_right _ h)),
    Or.inl (fun h => hn.2 (Finset.mem_union_left _ h))⟩

end AKLT.W.H1M023
