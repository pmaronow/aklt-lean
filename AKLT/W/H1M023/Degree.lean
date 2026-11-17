module
public import AKLT.W.H1M023.Count

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.H1M023

open AKLT.Blueprint.H1

private def internalDegree (m : LocalVariable →₀ ℕ) (x : Plane) : ℕ :=
  ∑ k : Fin 3, m (.inl (x, k))

private lemma internalDegree_add (m n : LocalVariable →₀ ℕ) (x : Plane) :
    internalDegree (m + n) x = internalDegree m x + internalDegree n x := by
  simp [internalDegree, Finsupp.add_apply, Finset.sum_add_distrib]

private def DegreeBound (p : LocalPolynomial) (x : Plane) (d : ℕ) : Prop :=
  ∀ m ∈ p.support, internalDegree m x ≤ d

private lemma degreeBound_add (p q : LocalPolynomial) (x : Plane) (a b : ℕ)
    (hp : DegreeBound p x a) (hq : DegreeBound q x b) :
    DegreeBound (p * q) x (a + b) := by
  intro m hm
  have hmem := MvPolynomial.support_mul p q hm
  rcases Finset.mem_add.mp hmem with ⟨m₁, hm₁, m₂, hm₂, rfl⟩
  exact (internalDegree_add m₁ m₂ x).le.trans (Nat.add_le_add (hp m₁ hm₁) (hq m₂ hm₂))

private lemma degreeBound_sum (p q : LocalPolynomial) (x : Plane) (a b : ℕ)
    (hp : DegreeBound p x a) (hq : DegreeBound q x b) :
    DegreeBound (p + q) x (max a b) := by
  intro m hm
  have hmem := MvPolynomial.support_add hm
  rcases Finset.mem_union.mp hmem with h | h
  · exact (hp m h).trans (Nat.le_max_left ..)
  · exact (hq m h).trans (Nat.le_max_right ..)

private lemma formalDot_support_terms (a b : Fin 3 → LocalVariable) {m : LocalVariable →₀ ℕ}
    (hm : m ∈ (formalDot a b).support) :
    ∃ k : Fin 3, m = Finsupp.single (a k) 1 + Finsupp.single (b k) 1 := by
  classical
  unfold formalDot at hm
  have hs := MvPolynomial.support_sum
    (s := (Finset.univ : Finset (Fin 3)))
    (f := fun k : Fin 3 => MvPolynomial.X (a k) * MvPolynomial.X (b k)) hm
  rcases Finset.mem_biUnion.mp hs with ⟨k, hk, hprod⟩
  have hmul := MvPolynomial.support_mul
    (MvPolynomial.X (a k)) (MvPolynomial.X (b k)) hprod
  rw [MvPolynomial.support_X, MvPolynomial.support_X] at hmul
  simp only [Finset.mem_add, Finset.mem_singleton] at hmul
  rcases hmul with ⟨m₁, rfl, m₂, rfl, rfl⟩
  exact ⟨k, rfl⟩

private lemma internalDegree_single_plane (x y : Plane) (k : Fin 3) :
    internalDegree (Finsupp.single (.inl (y, k)) 1) x = if x = y then 1 else 0 := by
  by_cases h : x = y
  · subst y
    simp [internalDegree, Finsupp.single_apply]
  · simp [internalDegree, h]

private lemma internalDegree_single_vector (x : Plane) (j : Fin 20) (k : Fin 3) :
    internalDegree (Finsupp.single (.inr (j, k)) 1) x = 0 := by
  simp [internalDegree]

private lemma degreeBound_formalDot_internal_internal (x y z : Plane) (_hyz : y ≠ z) :
    DegreeBound (formalDot (fun k => .inl (y, k)) (fun k => .inl (z, k))) x
      ((if x = y then 1 else 0) + (if x = z then 1 else 0)) := by
  intro m hm
  obtain ⟨k, rfl⟩ := formalDot_support_terms _ _ hm
  rw [internalDegree_add, internalDegree_single_plane, internalDegree_single_plane]

private lemma degreeBound_formalDot_internal_vector (x y : Plane) (j : Fin 20) :
    DegreeBound (formalDot (fun k => .inl (y, k)) (fun k => .inr (j, k))) x
      (if x = y then 1 else 0) := by
  intro m hm
  obtain ⟨k, rfl⟩ := formalDot_support_terms _ _ hm
  rw [internalDegree_add, internalDegree_single_plane, internalDegree_single_vector]
  omega

private lemma degreeBound_one (x : Plane) : DegreeBound (1 : LocalPolynomial) x 0 := by
  intro m hm
  rw [MvPolynomial.support_one] at hm
  simp only [Finset.mem_singleton] at hm
  rw [hm]
  simp [internalDegree]

private lemma degreeBound_smul (c : ℚ) (p : LocalPolynomial) (x : Plane) (d : ℕ)
    (hp : DegreeBound p x d) : DegreeBound (c • p) x d := by
  intro m hm
  exact hp m (MvPolynomial.support_smul hm)

private lemma degreeBound_C_mul (c : ℚ) (p : LocalPolynomial) (x : Plane) (d : ℕ)
    (hp : DegreeBound p x d) : DegreeBound (MvPolynomial.C c * p) x d := by
  rw [MvPolynomial.C_mul']
  exact degreeBound_smul c p x d hp

private lemma degreeBound_bond_factor (x y z : Plane) (hyz : y ≠ z) :
    DegreeBound (1 + formalDot (fun k => .inl (y, k)) (fun k => .inl (z, k))) x
      (if x = y ∨ x = z then 1 else 0) := by
  have hdot := degreeBound_formalDot_internal_internal x y z hyz
  intro m hm
  have h := degreeBound_sum (1 : LocalPolynomial)
    (formalDot (fun k => .inl (y, k)) (fun k => .inl (z, k))) x 0
    ((if x = y then 1 else 0) + (if x = z then 1 else 0))
    (degreeBound_one x) hdot m hm
  have hc : max 0 ((if x = y then 1 else 0) + (if x = z then 1 else 0)) =
      (if x = y ∨ x = z then 1 else 0) := by
    by_cases hxy : x = y <;> by_cases hxz : x = z <;> simp_all
  rw [← hc]
  exact h

private lemma degreeBound_vector_factor (x y : Plane) (j : Fin 20) :
    DegreeBound (1 + formalDot (fun k => .inl (y, k)) (fun k => .inr (j, k))) x
      (if x = y then 1 else 0) := by
  have hdot := degreeBound_formalDot_internal_vector x y j
  intro m hm
  have h := degreeBound_sum (1 : LocalPolynomial)
    (formalDot (fun k => .inl (y, k)) (fun k => .inr (j, k))) x 0
    (if x = y then 1 else 0) (degreeBound_one x) hdot m hm
  have hc : max 0 (if x = y then 1 else 0) = (if x = y then 1 else 0) := by
    by_cases hxy : x = y <;> simp [hxy]
  rw [hc] at h
  exact h

private lemma degreeBound_mono {p : LocalPolynomial} {x : Plane} {a b : ℕ}
    (hp : DegreeBound p x a) (h : a ≤ b) : DegreeBound p x b := by
  intro m hm
  exact (hp m hm).trans h

private lemma degreeBound_prod {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → LocalPolynomial) (d : ι → ℕ) (x : Plane)
    (h : ∀ i ∈ s, DegreeBound (f i) x (d i)) :
    DegreeBound (∏ i ∈ s, f i) x (∑ i ∈ s, d i) := by
  induction s using Finset.induction_on with
  | empty => simpa using degreeBound_one x
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi]
      exact degreeBound_add _ _ _ _ _ (h i (Finset.mem_insert_self i s))
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

private lemma bond_factor_bound (π : PatternData) (r : Representation)
    (next : Bool) (x : Plane) {e : Plane × Plane} (he : e ∈ π.bonds) :
    DegreeBound
      (if e.1 ∈ reducedSpinSites π r ∧ e.2 ∈ reducedSpinSites π r ∧
          ¬ (next ∧ ({e.1, e.2} : Finset Plane) = {(0, 0), π.outgoing.step}) then
        1 + formalDot (fun k => .inl (e.1, k)) (fun k => .inl (e.2, k)) else 1)
      x (bondCost π r x e) := by
  classical
  split
  · rename_i hc
    have hd := degreeBound_bond_factor x e.1 e.2 (bond_info π he).2.2.1
    simpa [bondCost, hc.1, hc.2.1, eq_comm] using hd
  · exact degreeBound_mono (degreeBound_one x) (Nat.zero_le _)

private lemma group_factor_bound (π : PatternData) (r : Representation)
    (x y : Plane) :
    DegreeBound
      (if groupIsPair π r y then
        (1 + formalDot (fun k => .inl (y, k)) (fun k => .inr (groupLeader y, k))) *
        (1 + formalDot (fun k => .inl (y, k)) (fun k => .inr (groupSecond y, k)))
      else 1 + MvPolynomial.C (replacementRadius π y) *
        formalDot (fun k => .inl (leafNeighbor π y, k))
          (fun k => .inr (groupLeader y, k)))
      x (pairCost π r x y + singleCost π r x y) := by
  by_cases hp : groupIsPair π r y = true
  · rw [ite_eq_left hp]
    have hd := degreeBound_add _ _ _ _ _
      (degreeBound_vector_factor x y (groupLeader y))
      (degreeBound_vector_factor x y (groupSecond y))
    by_cases hx : x = y <;> simpa [pairCost, singleCost, hp, hx] using hd
  · have hp : groupIsPair π r y = false := Bool.eq_false_iff.mpr hp
    rw [ite_eq_right (by simp [hp])]
    have hd := degreeBound_sum _ _ _ _ _ (degreeBound_one x)
      (degreeBound_C_mul (replacementRadius π y) _ _ _
        (degreeBound_formalDot_internal_vector x (leafNeighbor π y) (groupLeader y)))
    simpa [pairCost, singleCost, hp] using hd

/-- Every surviving factor is charged to an original bond or a retained corner slot. -/
theorem reducedIntegrand_degreeBudget (π : PatternData) (r : Representation)
    (next : Bool) (x : Plane) :
    ∀ m ∈ (reducedIntegrand π r next).support,
      (∑ k : Fin 3, m (.inl (x, k))) ≤ degreeBudget π r x := by
  change DegreeBound (reducedIntegrand π r next) x (degreeBudget π r x)
  unfold reducedIntegrand degreeBudget
  apply degreeBound_add
  · exact degreeBound_prod π.bonds _ _ x (fun e he => bond_factor_bound π r next x he)
  · exact degreeBound_prod (reductionGroups π) _ _ x (fun y _ => group_factor_bound π r x y)

/-- The degree and spin-support bounds hold for arbitrary raw pattern data. -/
theorem reducedIntegrand_admissible (π : PatternData) (r : Representation) (next : Bool) :
    InternalAdmissible (reducedSpinSites π r) (reducedIntegrand π r next) := by
  constructor
  · intro m hm x hx k
    have hd := reducedIntegrand_degreeBudget π r next x m hm
    rw [degreeBudget_zero π r x hx] at hd
    have hk : m (.inl (x, k)) ≤ ∑ j : Fin 3, m (.inl (x, j)) :=
      Finset.single_le_sum (f := fun j => m (.inl (x, j)))
        (fun j _ => Nat.zero_le _) (Finset.mem_univ k)
    exact Nat.eq_zero_of_le_zero (hk.trans hd)
  · intro m hm x
    exact (reducedIntegrand_degreeBudget π r next x m hm).trans (degreeBudget_le_four π r x)

end AKLT.W.H1M023
