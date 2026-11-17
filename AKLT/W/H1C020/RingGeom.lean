module
public import AKLT.W.H1C020.Site
public import AKLT.W.H1C020.GroupTokens
public import AKLT.W.H1M023.Geometry
public import AKLT.W.H1C031.Geometry
public import AKLT.W.H1M006.Geometry

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-!
Template geometry used by the ring contraction: the eight ring positions,
retained sites, the bonds incident to a corner or a tip, and the unique
neighbor of a replaced leaf.
-/

noncomputable section
open scoped BigOperators

namespace AKLT.W.H1C020

open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

lemma presentBond_iff (π : PatternData) (a b : Plane) :
    presentBond π a b = true ↔ ((a,b) ∈ π.bonds ∨ (b,a) ∈ π.bonds) := by
  simp [presentBond]

lemma presentBond_comm (π : PatternData) (a b : Plane) :
    presentBond π a b = presentBond π b a :=
  AKLT.W.H1C031.presentBond_symm π a b

lemma ptOf_ne_origin (i : Nat) (hi : i < 8) : ptOf i ≠ (0,0) := by
  interval_cases i <;> simp [ptOf, ringSites]

lemma ptOf_not_tip (i : Nat) (hi : i < 8) : ptOf i ∉ templateTips := by
  interval_cases i <;> simp [ptOf, ringSites, templateTips]

lemma ptOf_corner_iff (i : Nat) (hi : i < 8) : ptOf i ∈ templateCorners ↔ i % 2 = 1 := by
  interval_cases i <;> simp [ptOf, ringSites, templateCorners]

lemma groupPoint_odd (i : Nat) (h : i % 2 = 1) : groupPoint i = ptOf i := by
  have : (i % 2 == 0) = false := by simp [h]
  simp [groupPoint, ptOf, this]

lemma groupPoint_ne_ptOf (i : Nat) (hi : i < 8) (he : i % 2 = 0) : ptOf i ≠ groupPoint i := by
  interval_cases i <;> simp_all [ptOf, groupPoint, ringSites]

lemma groupPoint_ne_origin (i : Nat) (hi : i < 8) : groupPoint i ≠ (0,0) := by
  interval_cases i <;> simp [groupPoint, ringSites]

lemma ptOf_left_index (i : Nat) (hi : i < 8) : ((i+1)%8 + 7) % 8 = i := by omega

lemma mem_reducedSpinSites (π : PatternData) (r : Representation) (x : Plane) :
    x ∈ reducedSpinSites π r ↔ x ∈ π.active ∧ x ∉ templateTips ∧
      (x ∉ templateCorners ∨ (patternDegree π x ≠ 0 ∧ ¬ SingleReplacement π r x)) := by
  classical
  unfold reducedSpinSites
  simp only [Finset.mem_filter]

lemma presentBond_active {π : PatternData} {a b : Plane} (h : presentBond π a b = true) :
    a ∈ π.active ∧ b ∈ π.active := by
  rcases (presentBond_iff π a b).mp h with h | h
  · have := AKLT.W.H1M023.bond_info π h
    exact ⟨this.1, this.2.1⟩
  · have := AKLT.W.H1M023.bond_info π h
    exact ⟨this.2.1, this.1⟩

lemma presentBond_degree {π : PatternData} {a b : Plane} (h : presentBond π a b = true) :
    0 < patternDegree π a ∧ 0 < patternDegree π b := by
  rcases (presentBond_iff π a b).mp h with h | h
  · exact ⟨Finset.card_pos.mpr ⟨(a,b), Finset.mem_filter.mpr ⟨h, Or.inl rfl⟩⟩,
      Finset.card_pos.mpr ⟨(a,b), Finset.mem_filter.mpr ⟨h, Or.inr rfl⟩⟩⟩
  · exact ⟨Finset.card_pos.mpr ⟨(b,a), Finset.mem_filter.mpr ⟨h, Or.inr rfl⟩⟩,
      Finset.card_pos.mpr ⟨(b,a), Finset.mem_filter.mpr ⟨h, Or.inl rfl⟩⟩⟩

lemma axial_mem_V (π : PatternData) (r : Representation) (i : Nat) (hi : i < 8)
    (he : i % 2 = 0) (hact : ptOf i ∈ π.active) : ptOf i ∈ reducedSpinSites π r := by
  rw [mem_reducedSpinSites]
  refine ⟨hact, ptOf_not_tip i hi, Or.inl ?_⟩
  rw [ptOf_corner_iff i hi]
  omega

lemma corner_mem_V (π : PatternData) (r : Representation) (c : Nat)
    (hdeg : 0 < patternDegree π (ptOf c)) (hns : ¬ SingleReplacement π r (ptOf c))
    (hc : c < 8) : ptOf c ∈ reducedSpinSites π r := by
  rw [mem_reducedSpinSites]
  exact ⟨AKLT.W.H1M023.positive_degree_active π hdeg, ptOf_not_tip c hc,
    Or.inr ⟨Nat.ne_of_gt hdeg, hns⟩⟩

lemma single_not_mem_V (π : PatternData) (r : Representation) (c : Nat)
    (hc : c < 8) (hodd : c % 2 = 1) (hs : SingleReplacement π r (ptOf c)) :
    ptOf c ∉ reducedSpinSites π r := by
  rw [mem_reducedSpinSites]
  rintro ⟨_, _, h⟩
  rcases h with h | h
  · exact h ((ptOf_corner_iff c hc).mpr hodd)
  · exact h.2 hs

lemma tip_not_mem_V (π : PatternData) (r : Representation) {x : Plane} (hx : x ∈ templateTips) :
    x ∉ reducedSpinSites π r := by
  rw [mem_reducedSpinSites]
  rintro ⟨_, h, _⟩
  exact h hx

lemma origin_mem_V (π : PatternData) (hπ : π.Covered) (r : Representation) :
    ((0,0) : Plane) ∈ reducedSpinSites π r := by
  rw [mem_reducedSpinSites]
  refine ⟨?_, by simp [templateTips], Or.inl (by simp [templateCorners])⟩
  rw [AKLT.W.H1M006.mem_active_iff, hπ.2.1]
  decide

/-- Every bond at a corner is one of its two ring bonds. -/
lemma corner_bond_cases (π : PatternData) (c : Nat) (hc : c < 8) (hodd : c % 2 = 1)
    {f : Plane × Plane} (hf : f ∈ π.bonds) (hx : f.1 = ptOf c ∨ f.2 = ptOf c) :
    (f.1 = ptOf (c-1) ∧ f.2 = ptOf c) ∨ (f.1 = ptOf c ∧ f.2 = ptOf (c-1)) ∨
      (f.1 = ptOf ((c+1)%8) ∧ f.2 = ptOf c) ∨ (f.1 = ptOf c ∧ f.2 = ptOf ((c+1)%8)) := by
  obtain ⟨⟨p1,p2⟩,⟨q1,q2⟩⟩ := f
  have hi := (Finset.mem_filter.mp hf).1
  rw [AKLT.W.H1C031.mem_internalBonds_iff] at hi
  obtain ⟨hp, hq, hdir⟩ := hi
  rw [AKLT.W.H1C031.mem_templateSites_iff] at hp hq
  simp only [latticeDist, Prod.mk.injEq, sub_zero] at hp hq hdir hx ⊢
  rcases hx with hx | hx <;> rcases hdir with hd | hd <;>
    interval_cases c <;> simp only [ptOf, ringSites, List.getD_cons_succ, List.getD_cons_zero,
      Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd, Prod.mk.injEq] at hodd hx ⊢ <;> omega

/-- Every bond at a tip joins it to its axial ring site. -/
lemma tip_bond_cases (π : PatternData) (i : Nat) (hi : i < 8) (he : i % 2 = 0)
    {f : Plane × Plane} (hf : f ∈ π.bonds) (hx : f.1 = groupPoint i ∨ f.2 = groupPoint i) :
    (f.1 = ptOf i ∧ f.2 = groupPoint i) ∨ (f.1 = groupPoint i ∧ f.2 = ptOf i) := by
  obtain ⟨⟨p1,p2⟩,⟨q1,q2⟩⟩ := f
  have hi' := (Finset.mem_filter.mp hf).1
  rw [AKLT.W.H1C031.mem_internalBonds_iff] at hi'
  obtain ⟨hp, hq, hdir⟩ := hi'
  rw [AKLT.W.H1C031.mem_templateSites_iff] at hp hq
  simp only [latticeDist, Prod.mk.injEq, sub_zero] at hp hq hdir hx ⊢
  interval_cases i <;> simp only [ptOf, groupPoint, ringSites, List.getD_cons_succ,
    List.getD_cons_zero, Nat.reduceMod, beq_self_eq_true, ↓reduceIte, Prod.mk.injEq,
    Nat.reduceBEq, Bool.false_eq_true] at he hx ⊢ <;> omega

lemma otherEnd_of_left {x y : Plane} {e : Plane × Plane} (h1 : e.1 = y) (h2 : e.2 = x)
    (hne : y ≠ x) : AKLT.W.H1M023.otherEnd x e = y := by
  unfold AKLT.W.H1M023.otherEnd
  rw [if_neg (by rw [h1]; exact hne), h1]

lemma otherEnd_of_right {x y : Plane} {e : Plane × Plane} (h1 : e.1 = x) (h2 : e.2 = y) :
    AKLT.W.H1M023.otherEnd x e = y := by
  unfold AKLT.W.H1M023.otherEnd
  rw [if_pos h1, h2]

/-- The replaced tip has its axial ring site as unique neighbor. -/
lemma tip_leafNeighbor (π : PatternData) (i : Nat) (hi : i < 8) (he : i % 2 = 0)
    (hg : groupPoint i ∈ reductionGroups π) : leafNeighbor π (groupPoint i) = ptOf i := by
  have hpos : 0 < patternDegree π (groupPoint i) := (Finset.mem_filter.mp hg).2
  have hle := AKLT.W.H1M023.pattern_tip_degree_bound π (even_groupPoint_tip i hi he)
  obtain ⟨e, he', hinc, hval, _⟩ :=
    AKLT.W.H1M023.leaf_bond π (by omega : patternDegree π (groupPoint i) = 1)
  rw [hval]
  rcases tip_bond_cases π i hi he he' hinc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact otherEnd_of_left h1 h2 (groupPoint_ne_ptOf i hi he)
  · exact otherEnd_of_right h1 h2

lemma ring_neighbors_ne (c : Nat) (hc : c < 8) (hodd : c % 2 = 1) :
    ptOf (c-1) ≠ ptOf ((c+1)%8) ∧ ptOf (c-1) ≠ ptOf c ∧ ptOf ((c+1)%8) ≠ ptOf c := by
  interval_cases c <;> simp_all [ptOf, ringSites]

/-- A replaced corner has exactly one of its two ring bonds, and its unique
neighbor is the other end of that bond. -/
lemma leaf_corner (π : PatternData) (r : Representation) (c : Nat) (hc : c < 8)
    (hodd : c % 2 = 1) (hs : SingleReplacement π r (ptOf c)) :
    (presentBond π (ptOf (c-1)) (ptOf c) = true ∧
        presentBond π (ptOf c) (ptOf ((c+1)%8)) = false ∧
        leafNeighbor π (ptOf c) = ptOf (c-1)) ∨
      (presentBond π (ptOf (c-1)) (ptOf c) = false ∧
        presentBond π (ptOf c) (ptOf ((c+1)%8)) = true ∧
        leafNeighbor π (ptOf c) = ptOf ((c+1)%8)) := by
  obtain ⟨e, he, hinc, hval, huniq⟩ := AKLT.W.H1M023.leaf_bond π hs.1
  obtain ⟨hne1, hne2, hne3⟩ := ring_neighbors_ne c hc hodd
  have hother : ∀ {a b : Plane}, presentBond π a b = true →
      (a = ptOf c ∨ b = ptOf c) → (a = e.1 ∧ b = e.2) ∨ (a = e.2 ∧ b = e.1) := by
    intro a b hab hx
    rcases (presentBond_iff π a b).mp hab with h | h
    · have := huniq (a,b) h hx
      left
      rw [← this]
      exact ⟨rfl, rfl⟩
    · have := huniq (b,a) h hx.symm
      right
      rw [← this]
      exact ⟨rfl, rfl⟩
  rcases corner_bond_cases π c hc hodd he hinc with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    refine ⟨(presentBond_iff π _ _).mpr (Or.inl (by rw [← h1, ← h2]; exact he)), ?_, ?_⟩
    · cases hb : presentBond π (ptOf c) (ptOf ((c+1)%8))
      · rfl
      · exfalso
        rcases hother hb (Or.inl rfl) with ⟨_, h⟩ | ⟨_, h⟩
        · exact hne3 (h.trans h2)
        · exact hne1 (h.trans h1).symm
    · rw [hval]; exact otherEnd_of_left h1 h2 hne2
  · left
    refine ⟨(presentBond_iff π _ _).mpr (Or.inr (by rw [← h1, ← h2]; exact he)), ?_, ?_⟩
    · cases hb : presentBond π (ptOf c) (ptOf ((c+1)%8))
      · rfl
      · exfalso
        rcases hother hb (Or.inl rfl) with ⟨_, h⟩ | ⟨_, h⟩
        · exact hne1 (h.trans h2).symm
        · exact hne3 (h.trans h1)
    · rw [hval]; exact otherEnd_of_right h1 h2
  · right
    refine ⟨?_, (presentBond_iff π _ _).mpr (Or.inr (by rw [← h1, ← h2]; exact he)), ?_⟩
    · cases hb : presentBond π (ptOf (c-1)) (ptOf c)
      · rfl
      · exfalso
        rcases hother hb (Or.inr rfl) with ⟨h, _⟩ | ⟨h, _⟩
        · exact hne1 (h.trans h1)
        · exact hne2 (h.trans h2)
    · rw [hval]; exact otherEnd_of_left h1 h2 hne3
  · right
    refine ⟨?_, (presentBond_iff π _ _).mpr (Or.inl (by rw [← h1, ← h2]; exact he)), ?_⟩
    · cases hb : presentBond π (ptOf (c-1)) (ptOf c)
      · rfl
      · exfalso
        rcases hother hb (Or.inr rfl) with ⟨h, _⟩ | ⟨h, _⟩
        · exact hne2 (h.trans h1)
        · exact hne1 (h.trans h2)
    · rw [hval]; exact otherEnd_of_right h1 h2

end AKLT.W.H1C020
