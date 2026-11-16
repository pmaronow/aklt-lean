import AKLT.W.H1M023.Geometry

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.H1M023

/-- One unit of degree for each surviving bond incident to the site. -/
def bondCost (π : PatternData) (r : Representation) (x : Plane) (e : Plane × Plane) : ℕ :=
  if e.1 ∈ reducedSpinSites π r ∧ e.2 ∈ reducedSpinSites π r ∧
      (e.1 = x ∨ e.2 = x) then 1 else 0

def pairCost (π : PatternData) (r : Representation) (x y : Plane) : ℕ :=
  if groupIsPair π r y then if x = y then 2 else 0 else 0

def singleCost (π : PatternData) (r : Representation) (x y : Plane) : ℕ :=
  if groupIsPair π r y then 0 else if x = leafNeighbour π y then 1 else 0

/-- Charge a replacement factor to the bond that it replaces. -/
def replacementCost (π : PatternData) (r : Representation) (x y : Plane)
    (e : Plane × Plane) : ℕ :=
  if groupIsPair π r y then 0 else
    if (e.1 = y ∨ e.2 = y) ∧ x = otherEnd y e then 1 else 0

/-- An upper bound on the separate internal degree before moment contraction. -/
def degreeBudget (π : PatternData) (r : Representation) (x : Plane) : ℕ :=
  (∑ e ∈ π.bonds, bondCost π r x e) +
    ∑ y ∈ reductionGroups π, (pairCost π r x y + singleCost π r x y)

private lemma otherEnd_reverse {e : Plane × Plane} (hne : e.1 ≠ e.2)
    {y : Plane} (hy : e.1 = y ∨ e.2 = y) :
    (e.1 = otherEnd y e ∨ e.2 = otherEnd y e) ∧
      otherEnd (otherEnd y e) e = y := by
  rcases hy with h | h <;> subst y <;> simp [otherEnd, hne, Ne.symm hne]

lemma singleCost_eq_sum (π : PatternData) (r : Representation) (x : Plane)
    {y : Plane} (hy : y ∈ reductionGroups π) :
    singleCost π r x y = ∑ e ∈ π.bonds, replacementCost π r x y e := by
  classical
  by_cases hp : groupIsPair π r y = true
  · simp [singleCost, replacementCost, hp]
  · have hp : groupIsPair π r y = false := Bool.eq_false_iff.mpr hp
    have hs := group_single π r hy hp
    obtain ⟨e, he, hei, hne, hu⟩ := leaf_bond π hs.1.1
    rw [Finset.sum_eq_single e]
    · simp [singleCost, replacementCost, hp, hei, hne]
    · intro f hf hfe
      have hni : ¬ (f.1 = y ∨ f.2 = y) := fun hi => hfe (hu f hf hi)
      simp [replacementCost, hp, hni]
    · exact fun hn => (hn he).elim

private lemma replacement_sum_le_one (π : PatternData) (r : Representation)
    (x : Plane) {e : Plane × Plane} (he : e ∈ π.bonds) :
    (∑ y ∈ reductionGroups π, replacementCost π r x y e) ≤ 1 := by
  classical
  calc
    _ ≤ ∑ y ∈ reductionGroups π, if y = otherEnd x e then 1 else 0 := by
      apply Finset.sum_le_sum
      intro y hy
      by_cases hp : groupIsPair π r y = true
      · simp [replacementCost, hp]
      · have hp : groupIsPair π r y = false := Bool.eq_false_iff.mpr hp
        by_cases hi : (e.1 = y ∨ e.2 = y) ∧ x = otherEnd y e
        · have hr := (otherEnd_reverse (bond_info π he).2.2.1 hi.1).2
          have heq : y = otherEnd x e := by rw [hi.2]; exact hr.symm
          simp only [replacementCost, hp, Bool.false_eq_true, ite_false,
            ite_eq_left hi, ite_eq_left heq, Nat.le_refl]
        · simp [replacementCost, hp, hi]
    _ ≤ 1 := by
      by_cases hm : otherEnd x e ∈ reductionGroups π <;> simp [hm]

private lemma replacement_sum_zero_retained (π : PatternData) (r : Representation)
    (x : Plane) {e : Plane × Plane}
    (hv : e.1 ∈ reducedSpinSites π r ∧ e.2 ∈ reducedSpinSites π r) :
    (∑ y ∈ reductionGroups π, replacementCost π r x y e) = 0 := by
  apply Finset.sum_eq_zero
  intro y hy
  by_cases hp : groupIsPair π r y = true
  · simp [replacementCost, hp]
  · have hp : groupIsPair π r y = false := Bool.eq_false_iff.mpr hp
    have hs := (group_single π r hy hp).2
    have hni : ¬ (e.1 = y ∨ e.2 = y) := by
      rintro (h | h)
      · exact hs (h ▸ hv.1)
      · exact hs (h ▸ hv.2)
    simp [replacementCost, hp, hni]

private lemma replacement_sum_zero_not_incident (π : PatternData) (r : Representation)
    (x : Plane) {e : Plane × Plane} (he : e ∈ π.bonds)
    (hx : ¬ (e.1 = x ∨ e.2 = x)) :
    (∑ y ∈ reductionGroups π, replacementCost π r x y e) = 0 := by
  apply Finset.sum_eq_zero
  intro y hy
  have hni : ¬ ((e.1 = y ∨ e.2 = y) ∧ x = otherEnd y e) := by
    rintro ⟨hi, rfl⟩
    exact hx (otherEnd_reverse (bond_info π he).2.2.1 hi).1
  simp [replacementCost, hni]

private lemma bond_charge_le (π : PatternData) (r : Representation) (x : Plane)
    {e : Plane × Plane} (he : e ∈ π.bonds) :
    bondCost π r x e + (∑ y ∈ reductionGroups π, replacementCost π r x y e) ≤
      if e.1 = x ∨ e.2 = x then 1 else 0 := by
  classical
  by_cases hv : e.1 ∈ reducedSpinSites π r ∧ e.2 ∈ reducedSpinSites π r
  · rw [replacement_sum_zero_retained π r x hv]
    simp [bondCost, hv]
  · have hc : bondCost π r x e = 0 := by
      exact ite_eq_right (fun h => hv ⟨h.1, h.2.1⟩)
    rw [hc, zero_add]
    by_cases hx : e.1 = x ∨ e.2 = x
    · simpa [hx] using replacement_sum_le_one π r x he
    · simp [hx, replacement_sum_zero_not_incident π r x he hx]

lemma bonds_and_singles_le (π : PatternData) (r : Representation) (x : Plane) :
    (∑ e ∈ π.bonds, bondCost π r x e) +
      (∑ y ∈ reductionGroups π, singleCost π r x y) ≤ patternDegree π x := by
  classical
  have hs : (∑ y ∈ reductionGroups π, singleCost π r x y) =
      ∑ y ∈ reductionGroups π, ∑ e ∈ π.bonds, replacementCost π r x y e := by
    exact Finset.sum_congr rfl (fun y hy => singleCost_eq_sum π r x hy)
  rw [hs, Finset.sum_comm, ← Finset.sum_add_distrib]
  calc
    _ ≤ ∑ e ∈ π.bonds, if e.1 = x ∨ e.2 = x then 1 else 0 :=
      Finset.sum_le_sum (fun e he => bond_charge_le π r x he)
    _ = patternDegree π x := by simp [Finset.sum_boole, patternDegree]

lemma pairs_le (π : PatternData) (r : Representation) (x : Plane) :
    (∑ y ∈ reductionGroups π, pairCost π r x y) ≤
      if x ∈ templateCorners then 2 else 0 := by
  classical
  by_cases hx : x ∈ templateCorners
  · simp only [hx, ite_true]
    calc
      _ ≤ ∑ y ∈ reductionGroups π, if x = y then 2 else 0 := by
        apply Finset.sum_le_sum
        intro y hy
        simp only [pairCost]
        split <;> simp_all
      _ ≤ 2 := by
        by_cases hm : x ∈ reductionGroups π <;> simp [hm]
  · simp only [hx, ite_false, Nat.le_zero]
    apply Finset.sum_eq_zero
    intro y hy
    by_cases hp : groupIsPair π r y = true
    · have hc : y ∈ templateCorners := by
        have hc : y ∈ templateCorners ∧ ¬ SingleReplacement π r y := by
          simpa [groupIsPair] using hp
        exact hc.1
      have hxy : x ≠ y := fun h => hx (h ▸ hc)
      simp [pairCost, hp, hxy]
    · simp [pairCost, hp]

lemma degreeBudget_le_four (π : PatternData) (r : Representation) (x : Plane) :
    degreeBudget π r x ≤ 4 := by
  have hb := bonds_and_singles_le π r x
  have hp := pairs_le π r x
  have hd := pattern_degree_bound π x
  unfold degreeBudget
  rw [Finset.sum_add_distrib]
  by_cases hx : x ∈ templateCorners <;> simp only [hx, ite_true, ite_false] at hp hd <;> omega

lemma degreeBudget_zero (π : PatternData) (r : Representation) (x : Plane)
    (hx : x ∉ reducedSpinSites π r) : degreeBudget π r x = 0 := by
  classical
  unfold degreeBudget
  have hb : (∑ e ∈ π.bonds, bondCost π r x e) = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    have hn : ¬ (e.1 ∈ reducedSpinSites π r ∧ e.2 ∈ reducedSpinSites π r ∧
        (e.1 = x ∨ e.2 = x)) := by
      rintro ⟨h1, h2, h | h⟩
      · exact hx (h ▸ h1)
      · exact hx (h ▸ h2)
    simp [bondCost, hn]
  rw [hb, zero_add]
  apply Finset.sum_eq_zero
  intro y hy
  by_cases hp : groupIsPair π r y = true
  · have hxy : x ≠ y := fun h => hx (h ▸ group_pair_retained π r hy hp)
    simp [pairCost, singleCost, hp, hxy]
  · have hp : groupIsPair π r y = false := Bool.eq_false_iff.mpr hp
    have hxy : x ≠ leafNeighbour π y := fun h =>
      hx (h ▸ group_single_neighbour_retained π r hy hp)
    simp [pairCost, singleCost, hp, hxy]

end AKLT.W.H1M023
