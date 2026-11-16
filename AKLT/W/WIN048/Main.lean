import AKLT.W.WIN048.Helpers

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.WIN048

/-- With at most four pins, one of the six letters has all pin factors positive. -/
theorem exists_halfLetter
    (hNorm : ∀ j : IcoLetter, normSq (icoVector j) ≤ 1)
    (G : Finset Plane) (τ : PinAssignment G) (x : Plane) :
    ∃ j : HalfLetter, ∀ e : originalLegs G, e.val.1 = x →
      0 < 1 + dot (τ e).val (icoVector (halfLetter j)) := by
  classical
  by_contra h
  push Not at h
  choose e he hle using h
  let f : HalfLetter → {e : originalLegs G // e.val.1 = x} := fun j => ⟨e j, he j⟩
  have hneg (j : HalfLetter) : icoVector (halfLetter j) = -(τ (e j)).val := by
    apply eq_neg_of_factor_zero (le_of_eq (τ (e j)).property) (hNorm _)
    exact le_antisymm (hle j) (factor_nonneg (le_of_eq (τ (e j)).property) (hNorm _))
  have hf : Function.Injective f := by
    intro j k h
    have heq : e j = e k := congrArg Subtype.val h
    apply halfLetter_injective
    change icoVector (halfLetter j) = icoVector (halfLetter k)
    rw [hneg j, hneg k, heq]
  have hcard := (Fintype.card_le_of_injective f hf).trans (local_legs_card_le G x)
  norm_num [HalfLetter] at hcard

theorem half_factor_pos
    (hNorm : ∀ j : IcoLetter, normSq (icoVector j) ≤ 1) (j k : HalfLetter) :
    0 < 1 + dot (icoVector (halfLetter j)) (icoVector (halfLetter k)) := by
  have hn := factor_nonneg (hNorm (halfLetter j)) (hNorm (halfLetter k))
  have hz : 1 + dot (icoVector (halfLetter j)) (icoVector (halfLetter k)) ≠ 0 := by
    intro h
    exact halfLetter_not_antipodal k j
      (eq_neg_of_factor_zero (hNorm _) (hNorm _) h)
  exact lt_of_le_of_ne hn (Ne.symm hz)

theorem extend_norm_le
    (hNorm : ∀ j : IcoLetter, normSq (icoVector j) ≤ 1)
    {D : Finset Plane} (σ : D → IcoLetter) (x : Plane) :
    normSq (extendIcoSpins σ x) ≤ 1 := by
  unfold extendIcoSpins
  split_ifs
  · exact hNorm _
  · norm_num [normSq, dot]

theorem internalBonds_endpoints {D : Finset Plane} {e : Plane × Plane}
    (he : e ∈ internalBonds D) : e.1 ∈ D ∧ e.2 ∈ D := by
  simp only [internalBonds, Finset.mem_biUnion, Finset.mem_image] at he
  obtain ⟨x, hx, y, hy, rfl⟩ := he
  exact ⟨hx, (Finset.mem_inter.mp hy).2⟩

/-- A positive summand exists even for the empty surviving volume. -/
theorem main : AKLT.Blueprint.Win.OriginalPositivityStatement := by
  classical
  intro hFacts G Y τ
  have hNorm : ∀ j : IcoLetter, normSq (icoVector j) ≤ 1 := by
    intro j
    exact hFacts.1 .U (Or.inl rfl) (some j) (by norm_num [spinWeight])
  let D := G \ Y
  have hChoice : ∀ x : D, ∃ j : HalfLetter, ∀ e : originalLegs G, e.val.1 = x.val →
      0 < 1 + dot (τ e).val (icoVector (halfLetter j)) := by
    intro x
    exact exists_halfLetter hNorm G τ x.val
  choose j hj using hChoice
  let σ : D → IcoLetter := fun x => halfLetter (j x)
  let B (n : D → IcoLetter) : ℝ :=
    ∏ e ∈ internalBonds D, (1 + dot (extendIcoSpins n e.1) (extendIcoSpins n e.2))
  let P (n : D → IcoLetter) : ℝ :=
    ∏ e : originalLegs G,
      if e.val.1 ∈ D then 1 + dot (τ e).val (extendIcoSpins n e.val.1) else 1
  have hBn (n : D → IcoLetter) : 0 ≤ B n := by
    apply Finset.prod_nonneg
    intro e _
    exact factor_nonneg (extend_norm_le hNorm n _) (extend_norm_le hNorm n _)
  have hPn (n : D → IcoLetter) : 0 ≤ P n := by
    apply Finset.prod_nonneg
    intro e _
    split_ifs
    · exact factor_nonneg (le_of_eq (τ e).property) (extend_norm_le hNorm n _)
    · norm_num
  have hBp : 0 < B σ := by
    apply Finset.prod_pos
    intro e he
    obtain ⟨h1, h2⟩ := internalBonds_endpoints he
    have hv1 : extendIcoSpins σ e.1 = icoVector (halfLetter (j ⟨e.1, h1⟩)) := by
      simp only [extendIcoSpins, dite_eq_left h1, σ]
    have hv2 : extendIcoSpins σ e.2 = icoVector (halfLetter (j ⟨e.2, h2⟩)) := by
      simp only [extendIcoSpins, dite_eq_left h2, σ]
    rw [hv1, hv2]
    exact half_factor_pos hNorm _ _
  have hPp : 0 < P σ := by
    apply Finset.prod_pos
    intro e _
    split_ifs with he
    · have hv : extendIcoSpins σ e.val.1 =
          icoVector (halfLetter (j ⟨e.val.1, he⟩)) := by
        simp only [extendIcoSpins, dite_eq_left he, σ]
      rw [hv]
      exact hj ⟨e.val.1, he⟩ e rfl
    · norm_num
  have hc : 0 < (1 / 12 : ℝ) ^ D.card := by positivity
  constructor
  · change 0 < ∑ n : D → IcoLetter, (1 / 12 : ℝ) ^ D.card * 1 * B n * P n
    simp only [mul_one]
    exact Finset.sum_pos'
      (fun n _ => mul_nonneg (mul_nonneg hc.le (hBn n)) (hPn n))
      ⟨σ, Finset.mem_univ _, mul_pos (mul_pos hc hBp) hPp⟩
  · change 0 < ∑ n : D → IcoLetter, (1 / 12 : ℝ) ^ D.card * 1 * B n
    simp only [mul_one]
    exact Finset.sum_pos' (fun n _ => mul_nonneg hc.le (hBn n))
      ⟨σ, Finset.mem_univ _, mul_pos hc hBp⟩

#print axioms exists_halfLetter
#print axioms half_factor_pos
#print axioms extend_norm_le
#print axioms internalBonds_endpoints
#print axioms main

end AKLT.W.WIN048
