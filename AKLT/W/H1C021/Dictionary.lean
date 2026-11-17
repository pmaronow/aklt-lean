module
public import AKLT.W.H1C021.Congruence
public import AKLT.W.H1C021.Rational

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-! Closing the pure monomial congruence: the color lists of the eight ring
groups are turned into a Pauli label on the reduction tokens, the monomial
product is identified with the corresponding Pauli monomial, and each local
form is identified with the local integer congruence of the exchange basis. -/

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

namespace AKLT.W.H1C021

/-! ### Ring geometry: the eight group points and their ring-site indices -/

/-- Ring-site index of a template group point; inverse of `groupPoint` on the template. -/
def groupSite (x : Plane) : Nat :=
  if x = (2,0) then 0 else if x = (1,1) then 1 else if x = (0,2) then 2 else
  if x = (-1,1) then 3 else if x = (-2,0) then 4 else if x = (-1,-1) then 5 else
  if x = (0,-2) then 6 else 7

theorem groupSite_groupPoint (i : Nat) (hi : i < 8) : groupSite (groupPoint i) = i := by
  interval_cases i <;> decide

theorem groupPoint_mem_template (i : Nat) (hi : i < 8) :
    groupPoint i ∈ templateCorners ∪ templateTips := by
  interval_cases i <;> decide

theorem groupSite_spec (x : Plane) (hx : x ∈ templateCorners ∪ templateTips) :
    groupSite x < 8 ∧ groupPoint (groupSite x) = x := by
  simp only [templateCorners, templateTips, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton] at hx
  rcases hx with ((rfl|rfl|rfl|rfl)|(rfl|rfl|rfl|rfl)) <;> decide

theorem ringLeader_groupSite (x : Plane) (hx : x ∈ templateCorners ∪ templateTips) :
    ringLeader (groupSite x) = (groupLeader x).val := by
  simp only [templateCorners, templateTips, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton] at hx
  rcases hx with ((rfl|rfl|rfl|rfl)|(rfl|rfl|rfl|rfl)) <;> decide

theorem groupLeader_le (x : Plane) : (groupLeader x).val ≤ 17 := by
  unfold groupLeader
  split_ifs <;> decide

theorem groupSecond_val (x : Plane) : (groupSecond x).val = (groupLeader x).val + 1 := by
  have h := groupLeader_le x
  simp only [groupSecond]
  omega

theorem reductionGroups_template (π : PatternData) (x : reductionGroups π) :
    x.val ∈ templateCorners ∪ templateTips :=
  (Finset.mem_filter.mp x.property).1

/-! ### Reindexing products -/

theorem list_range_prod {M : Type*} [CommMonoid M] (F : Nat → M) (n : Nat) :
    ((List.range n).map F).prod = ∏ i ∈ Finset.range n, F i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.prod_range_succ, Finset.prod_range_succ, ih]

/-- A product over the eight ring sites, trivial off the reduction groups, is a
product over the reduction groups. -/
theorem prod_sites_eq_prod_groups {M : Type*} [CommMonoid M] (π : PatternData)
    (F : Nat → M) (hF : ∀ i < 8, groupPoint i ∉ reductionGroups π → F i = 1) :
    ((List.range 8).map F).prod = ∏ x : reductionGroups π, F (groupSite x.val) := by
  rw [Finset.prod_coe_sort (reductionGroups π) (fun x => F (groupSite x))]
  have hsub : reductionGroups π ⊆ templateCorners ∪ templateTips := Finset.filter_subset _ _
  rw [Finset.prod_subset hsub (fun x hx hn => hF _ (groupSite_spec x hx).1
    (by rw [(groupSite_spec x hx).2]; exact hn))]
  rw [list_range_prod]
  symm
  apply Finset.prod_nbij' groupSite groupPoint
  · intro x hx
    exact Finset.mem_range.mpr (groupSite_spec x hx).1
  · intro i hi
    exact groupPoint_mem_template i (Finset.mem_range.mp hi)
  · intro x hx
    exact (groupSite_spec x hx).2
  · intro i hi
    exact groupSite_groupPoint i (Finset.mem_range.mp hi)
  · intro x _
    rfl

/-- A product over the reduction tokens is a product over groups and their slots. -/
theorem prod_tokens_eq_prod_groups {M : Type*} [CommMonoid M] (π : PatternData)
    (r : Representation) (f : reductionVectors π r → M) :
    ∏ j, f j = ∏ x : reductionGroups π, ∏ k : GroupSlot π r x, f (groupSlotToken π r x k) := by
  rw [← Fintype.prod_sigma (fun xk : Σ x, GroupSlot π r x => f (groupSlotToken π r xk.1 xk.2))]
  exact (Fintype.prod_equiv (groupSlotEquiv π r) _ _ (fun xk => rfl)).symm

theorem formProduct_range (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (a b : ExchangeBasis π r ε) (site : Nat) (css : List (List Nat)) :
    formProduct π r ε a b site css = ((List.range css.length).map (fun i =>
      gaussianValue (localForm (css.getD i [])
        (groupDigit π r ε a (groupPoint (site+i)))
        (groupDigit π r ε b (groupPoint (site+i)))))).prod := by
  induction css generalizing site with
  | nil => simp [formProduct]
  | cons cs css ih =>
    rw [formProduct, ih, List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.prod_cons, List.map_map]
    congr 1
    apply congrArg List.prod
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply, List.getD_cons_succ]
    rw [show site + (i+1) = site + 1 + i by omega]

theorem monomialProduct_range (site : Nat) (css : List (List Nat)) :
    monomialProduct site css = ((List.range css.length).map (fun i =>
      vectorMonomial (ringLeader (site+i)) (css.getD i []))).prod := by
  induction css generalizing site with
  | nil => simp [monomialProduct]
  | cons cs css ih =>
    rw [monomialProduct, ih, List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.prod_cons, List.map_map]
    congr 1
    apply congrArg List.prod
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply, List.getD_cons_succ]
    rw [show site + (i+1) = site + 1 + i by omega]

/-! ### Products over the slots of one group -/

theorem slot_prod_one {M : Type*} [CommMonoid M] {N : Nat} (hN : N = 1) (z : Fin N)
    (f : Fin N → M) : ∏ k, f k = f z := by
  subst hN
  have hz : z = 0 := Subsingleton.elim _ _
  subst hz
  exact Fin.prod_univ_one f

theorem slot_prod_two {M : Type*} [CommMonoid M] {N : Nat} (hN : N = 2) (z l : Fin N)
    (hz : z.val = 0) (hl : l.val = 1) (f : Fin N → M) : ∏ k, f k = f z * f l := by
  subst hN
  have hz' : z = 0 := Fin.ext hz
  have hl' : l = 1 := Fin.ext hl
  subst hz' hl'
  exact Fin.prod_univ_two f

theorem slot_sum_one {N : Nat} (hN : N = 1) (z l : Fin N) (D : Fin N → Fin 4)
    (cA cB : Fin 2 → Fin 2 → ℂ) :
    (∑ s : Fin N → Fin 2, ∑ t : Fin N → Fin 2,
      cA (s z) (s l) * (∏ k, pauli (D k) (s k) (t k)) * cB (t z) (t l)) =
      ∑ i : Fin 2, ∑ j : Fin 2, cA i i * pauli (D z) i j * cB j j := by
  subst hN
  have hz : z = 0 := Subsingleton.elim _ _
  have hl : l = 0 := Subsingleton.elim _ _
  subst hz hl
  apply Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 2))
  intro s
  apply Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 2))
  intro t
  rw [Fin.prod_univ_one]
  rfl

theorem slot_sum_two {N : Nat} (hN : N = 2) (z l : Fin N) (hz : z.val = 0) (hl : l.val = 1)
    (D : Fin N → Fin 4) (cA cB : Fin 2 → Fin 2 → ℂ) :
    (∑ s : Fin N → Fin 2, ∑ t : Fin N → Fin 2,
      cA (s z) (s l) * (∏ k, pauli (D k) (s k) (t k)) * cB (t z) (t l)) =
      ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, ∑ m : Fin 2,
        cA i j * (pauli (D z) i k * pauli (D l) j m) * cB k m := by
  subst hN
  have hz' : z = 0 := Fin.ext hz
  have hl' : l = 1 := Fin.ext hl
  subst hz' hl'
  calc
    _ = ∑ p : Fin 2 × Fin 2, ∑ q : Fin 2 × Fin 2,
        cA p.1 p.2 * (pauli (D 0) p.1 q.1 * pauli (D 1) p.2 q.2) * cB q.1 q.2 := by
      apply Fintype.sum_equiv (finTwoArrowEquiv (Fin 2))
      intro s
      apply Fintype.sum_equiv (finTwoArrowEquiv (Fin 2))
      intro t
      rw [Fin.prod_univ_two]
      rfl
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Fintype.sum_prod_type]

/-! ### The Pauli label determined by the color lists -/

/-- Color list of the ring site carrying a group point. -/
def colourList (css : List (List Nat)) (x : Plane) : List Nat := css.getD (groupSite x) []

/-- The color at one slot of one group, as a Pauli label. -/
def slotColour (π : PatternData) (r : Representation) (css : List (List Nat))
    (p : Σ x : reductionGroups π, GroupSlot π r x) : Fin 4 :=
  ⟨(colourList css p.1.val).getD p.2.val 0 % 4, Nat.mod_lt _ (by norm_num)⟩

/-- The Pauli label of every reduction token, read from its group's color list. -/
def colourLabel (π : PatternData) (r : Representation) (css : List (List Nat)) :
    reductionVectors π r → Fin 4 := fun j =>
  slotColour π r css ((groupSlotEquiv π r).symm j)

theorem colourLabel_token (π : PatternData) (r : Representation) (css : List (List Nat))
    (x : reductionGroups π) (k : GroupSlot π r x) :
    colourLabel π r css (groupSlotToken π r x k) =
      ⟨(colourList css x.val).getD k.val 0 % 4, Nat.mod_lt _ (by norm_num)⟩ := by
  have h : (groupSlotEquiv π r).symm (groupSlotToken π r x k) = ⟨x, k⟩ := by
    rw [← groupSlotEquiv_apply]
    exact (groupSlotEquiv π r).symm_apply_apply _
  unfold colourLabel
  rw [h]
  rfl

/-! ### Pauli monomials as products of token factors -/

/-- The factor of one token: `1` for the identity label, otherwise one variable. -/
def pauliFactor (j : Fin 20) (c : Fin 4) : VectorPolynomial :=
  if c.val = 0 then 1 else vectorVariable j.val c.val

/-- Exponent of one token factor. -/
def pauliFactorExponent (j : Fin 20) (c : Fin 4) : (Fin 20 × Fin 3) →₀ ℕ :=
  if c.val = 0 then 0 else Finsupp.single (j, ⟨c.val - 1, by have := c.isLt; omega⟩) 1

theorem pauliFactor_monomial (j : Fin 20) (c : Fin 4) :
    pauliFactor j c = MvPolynomial.monomial (pauliFactorExponent j c) 1 := by
  unfold pauliFactor pauliFactorExponent
  split
  · rw [← MvPolynomial.C_apply, MvPolynomial.C_1]
  · rename_i hc
    unfold vectorVariable
    have h1 : (⟨j.val % 20, Nat.mod_lt _ (by decide)⟩ : Fin 20) = j :=
      Fin.ext (Nat.mod_eq_of_lt j.isLt)
    have h2 : (⟨(c.val - 1) % 3, Nat.mod_lt _ (by decide)⟩ : Fin 3) =
        ⟨c.val - 1, by have := c.isLt; omega⟩ :=
      Fin.ext (Nat.mod_eq_of_lt (by have := c.isLt; omega))
    rw [h1, h2]
    rfl

theorem pauliExponent_eq_sum (J : Finset (Fin 20)) (d : J → Fin 4) :
    pauliExponent J d = ∑ j : J, pauliFactorExponent j.val (d j) := by
  classical
  ext ⟨t, k⟩
  rw [Finsupp.finsetSum_apply, AKLT.W.H1M047.pauliExponent_apply]
  by_cases ht : t ∈ J
  · rw [dite_eq_left ht, Finset.sum_eq_single (⟨t, ht⟩ : J)]
    · simp only [pauliFactorExponent]
      have hd := (d ⟨t, ht⟩).isLt
      have hk := k.isLt
      split_ifs with h1 h2 h2
      · omega
      · rw [Finsupp.single_apply, ite_eq_left]
        ext
        · rfl
        · simp only
          omega
      · simp
      · rw [Finsupp.single_apply, ite_eq_right]
        intro h
        apply h1
        have := congrArg (fun p : Fin 20 × Fin 3 => p.2.val) h
        simp only at this
        omega
    · intro j _ hj
      simp only [pauliFactorExponent]
      split_ifs
      · simp
      · rw [Finsupp.single_apply, ite_eq_right]
        intro h
        apply hj
        apply Subtype.ext
        exact congrArg Prod.fst h
    · simp
  · rw [dite_eq_right ht]
    symm
    apply Finset.sum_eq_zero
    intro j _
    simp only [pauliFactorExponent]
    split_ifs
    · simp
    · rw [Finsupp.single_apply, ite_eq_right]
      intro h
      apply ht
      have := congrArg Prod.fst h
      simp only at this
      rw [← this]
      exact j.property

theorem pauliMonomial_eq_prod (J : Finset (Fin 20)) (d : J → Fin 4) :
    MvPolynomial.monomial (pauliExponent J d) (1 : ℚ) = ∏ j : J, pauliFactor j.val (d j) := by
  rw [pauliExponent_eq_sum, MvPolynomial.monomial_sum_one]
  apply Finset.prod_congr rfl
  intro j _
  rw [pauliFactor_monomial]

theorem pauliFactor_colour (j : Fin 20) (c : Nat) (hc : c < 4) :
    pauliFactor j ⟨c % 4, Nat.mod_lt _ (by norm_num)⟩ =
      if c == 0 then 1 else vectorVariable j.val c := by
  simp only [pauliFactor, Nat.mod_eq_of_lt hc, beq_iff_eq]

/-! ### One group: polynomial side -/

theorem groupSlotZero_val (π : PatternData) (r : Representation) (x : reductionGroups π) :
    (groupSlotZero π r x).val = 0 := rfl

theorem groupSlotLast_val (π : PatternData) (r : Representation) (x : reductionGroups π)
    (hp : groupIsPair π r x.val = true) : (groupSlotLast π r x).val = 1 := by
  unfold groupSlotLast
  rw [dite_eq_left hp]

theorem groupSlotToken_zero_val (π : PatternData) (r : Representation) (x : reductionGroups π) :
    (groupSlotToken π r x (groupSlotZero π r x)).val = groupLeader x.val := by
  rw [groupSlotToken_zero]
  rfl

theorem groupSlotToken_last_val (π : PatternData) (r : Representation) (x : reductionGroups π)
    (hp : groupIsPair π r x.val = true) :
    (groupSlotToken π r x (groupSlotLast π r x)).val = groupSecond x.val := by
  rw [groupSlotToken_last]
  simp only [AKLT.W.H1M032.secondOrLeader, hp, ↓reduceDIte, secondToken]

theorem vectorMonomial_group (π : PatternData) (r : Representation) (css : List (List Nat))
    (x : reductionGroups π)
    (hlen : (colourList css x.val).length = if groupIsPair π r x.val then 2 else 1)
    (hb : ∀ c ∈ colourList css x.val, c < 4) :
    vectorMonomial (groupLeader x.val).val (colourList css x.val) =
      ∏ k : GroupSlot π r x, pauliFactor (groupSlotToken π r x k).val
        (colourLabel π r css (groupSlotToken π r x k)) := by
  by_cases hp : groupIsPair π r x.val = true
  · rw [slot_prod_two (by simp only [hp, ↓reduceIte]) (groupSlotZero π r x)
      (groupSlotLast π r x) (groupSlotZero_val π r x) (groupSlotLast_val π r x hp)]
    rw [colourLabel_token, colourLabel_token, groupSlotToken_zero_val,
      groupSlotToken_last_val π r x hp, groupSlotZero_val, groupSlotLast_val π r x hp]
    rw [ite_eq_left hp] at hlen
    obtain ⟨c, e, hce⟩ := List.length_eq_two.mp hlen
    rw [hce] at hb ⊢
    have hc : c < 4 := hb c (by simp)
    have he : e < 4 := hb e (by simp)
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    rw [pauliFactor_colour _ _ hc, pauliFactor_colour _ _ he]
    have hs : (groupSecond x.val).val = (groupLeader x.val).val + 1 := groupSecond_val x.val
    simp only [vectorMonomial, hs, mul_one]
  · rw [slot_prod_one (by simp only [hp, Bool.false_eq_true, ↓reduceIte]) (groupSlotZero π r x)]
    rw [colourLabel_token, groupSlotToken_zero_val, groupSlotZero_val]
    rw [ite_eq_right hp] at hlen
    obtain ⟨c, hc1⟩ := List.length_eq_one_iff.mp hlen
    rw [hc1] at hb ⊢
    have hc : c < 4 := hb c (by simp)
    simp only [List.getD_cons_zero]
    rw [pauliFactor_colour _ _ hc]
    simp only [vectorMonomial, mul_one]

/-! ### One group: form side -/

theorem pairCoeff_localVector (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (a : ExchangeBasis π r ε) (x : reductionGroups π) (hp : groupIsPair π r x.val = true)
    (i j : Fin 2) :
    pairCoeff (groupDigit π r ε a x.val) i j =
      AKLT.W.H1M032.localVector (groupIsPair π r x.val)
        (π.statusAt x.val = .D ∧ ε x = false) (a x).val i j := by
  have ha := (a x).isLt
  have hdig : groupDigit π r ε a x.val =
      if π.statusAt x.val = .D ∧ ε x = false then 3 else (a x).val := by
    unfold groupDigit
    rw [dite_eq_left x.property]
    simp only [hp, Bool.true_and, decide_eq_true_eq, Subtype.coe_eta]
  rw [hdig]
  simp only [AKLT.W.H1M032.localVector, hp, ↓reduceIte]
  by_cases hE : π.statusAt x.val = .D ∧ ε x = false
  · simp only [hE, and_self, ↓reduceIte, pairCoeff]
    norm_num
  · simp only [hE, ↓reduceIte]
    change (a x).val < (if groupIsPair π r x.val then
      if π.statusAt x.val = .D ∧ ε x = false then 1 else 3 else 2) at ha
    simp only [hp, hE, ↓reduceIte] at ha
    generalize (a x).val = v at ha ⊢
    interval_cases v <;> simp [pairCoeff]

theorem single_digit (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (a : ExchangeBasis π r ε) (x : reductionGroups π) (hp : ¬ groupIsPair π r x.val = true) :
    groupDigit π r ε a x.val = (a x).val ∧ (a x).val < 2 := by
  have ha0 := (a x).isLt
  change (a x).val < (if groupIsPair π r x.val then
      if π.statusAt x.val = .D ∧ ε x = false then 1 else 3 else 2) at ha0
  have ha : (a x).val < 2 := ha0.trans_eq (ite_eq_right hp)
  refine ⟨?_, ha⟩
  unfold groupDigit
  rw [dite_eq_left x.property]
  simp only [Bool.eq_false_iff.mpr hp, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    Subtype.coe_eta]

theorem single_sum (A B : Nat) (hA : A < 2) (hB : B < 2) (P : Matrix (Fin 2) (Fin 2) ℂ) :
    (∑ i : Fin 2, ∑ j : Fin 2,
      ((if i.val = A then 1 else 0 : ℤ) : ℂ) * P i j * ((if j.val = B then 1 else 0 : ℤ) : ℂ)) =
      P ⟨A, hA⟩ ⟨B, hB⟩ := by
  interval_cases A <;> interval_cases B <;> simp [Fin.sum_univ_two]

theorem localForm_group (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (css : List (List Nat)) (a b : ExchangeBasis π r ε) (x : reductionGroups π)
    (hlen : (colourList css x.val).length = if groupIsPair π r x.val then 2 else 1)
    (hb : ∀ c ∈ colourList css x.val, c < 4) :
    gaussianValue (localForm (colourList css x.val)
      (groupDigit π r ε a x.val) (groupDigit π r ε b x.val)) =
      ∑ s : GroupSlot π r x → Fin 2, ∑ t : GroupSlot π r x → Fin 2,
        (groupBasisCoeff π r ε a x s : ℂ) *
          (∏ k, pauli (colourLabel π r css (groupSlotToken π r x k)) (s k) (t k)) *
            (groupBasisCoeff π r ε b x t : ℂ) := by
  by_cases hp : groupIsPair π r x.val = true
  · refine Eq.trans ?_ (slot_sum_two (by simp only [hp, ↓reduceIte]) (groupSlotZero π r x)
      (groupSlotLast π r x) (groupSlotZero_val π r x) (groupSlotLast_val π r x hp)
      (fun k => colourLabel π r css (groupSlotToken π r x k))
      (fun i j => ((AKLT.W.H1M032.localVector (groupIsPair π r x.val)
        (π.statusAt x.val = .D ∧ ε x = false) (a x).val i j : ℤ) : ℂ))
      (fun i j => ((AKLT.W.H1M032.localVector (groupIsPair π r x.val)
        (π.statusAt x.val = .D ∧ ε x = false) (b x).val i j : ℤ) : ℂ))).symm
    simp only [colourLabel_token, groupSlotZero_val, groupSlotLast_val π r x hp]
    rw [ite_eq_left hp] at hlen
    obtain ⟨c, e, hce⟩ := List.length_eq_two.mp hlen
    rw [hce] at hb ⊢
    have hc : c < 4 := hb c (by simp)
    have he : e < 4 := hb e (by simp)
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    have hform : localForm [c, e] (groupDigit π r ε a x.val) (groupDigit π r ε b x.val) =
        pairForm (⟨c % 4, Nat.mod_lt _ (by norm_num)⟩ : Fin 4).val
          (⟨e % 4, Nat.mod_lt _ (by norm_num)⟩ : Fin 4).val
          (groupDigit π r ε a x.val) (groupDigit π r ε b x.val) := by
      simp only [localForm, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt he]
    rw [hform, pairForm_value]
    simp only [pairCoeff_localVector π r ε a x hp, pairCoeff_localVector π r ε b x hp]
  · refine Eq.trans ?_ (slot_sum_one (by simp only [hp, Bool.false_eq_true, ↓reduceIte])
      (groupSlotZero π r x) (groupSlotLast π r x)
      (fun k => colourLabel π r css (groupSlotToken π r x k))
      (fun i j => ((AKLT.W.H1M032.localVector (groupIsPair π r x.val)
        (π.statusAt x.val = .D ∧ ε x = false) (a x).val i j : ℤ) : ℂ))
      (fun i j => ((AKLT.W.H1M032.localVector (groupIsPair π r x.val)
        (π.statusAt x.val = .D ∧ ε x = false) (b x).val i j : ℤ) : ℂ))).symm
    simp only [colourLabel_token, groupSlotZero_val]
    rw [ite_eq_right hp] at hlen
    obtain ⟨c, hc1⟩ := List.length_eq_one_iff.mp hlen
    rw [hc1] at hb ⊢
    have hc : c < 4 := hb c (by simp)
    simp only [List.getD_cons_zero]
    obtain ⟨hda, ha⟩ := single_digit π r ε a x hp
    obtain ⟨hdb, hb'⟩ := single_digit π r ε b x hp
    have hP : groupIsPair π r x.val = false := Bool.eq_false_iff.mpr hp
    simp only [AKLT.W.H1M032.localVector, hP, Bool.false_eq_true, ↓reduceIte]
    have hcf : (⟨c % 4, Nat.mod_lt _ (by norm_num)⟩ : Fin 4) = ⟨c, hc⟩ :=
      Fin.ext (Nat.mod_eq_of_lt hc)
    rw [hcf, single_sum _ _ ha hb', hda, hdb]
    simp only [localForm]
    exact pauliZ_value ⟨c, hc⟩ ⟨(a x).val, ha⟩ ⟨(b x).val, hb'⟩

/-! ### The monomial congruence -/

theorem monomialCongruence : Residual_monomialCongruence := by
  classical
  intro π r ε a b css hl8 hshape hbound
  have hsite : ∀ i < 8, (css.getD i []).length = groupSlots π r (groupPoint i) := by
    intro i hi
    have h := List.getElem_of_eq hshape (i := i) (by simp [hl8, hi])
    simp only [List.getElem_map, List.getElem_range] at h
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact h
  have hcol : ∀ i < 8, ∀ c ∈ css.getD i [], c < 4 := by
    intro i hi c hc
    rw [List.getD_eq_getElem _ _ (by omega)] at hc
    exact hbound _ (List.getElem_mem _) c hc
  have hnil : ∀ i < 8, groupPoint i ∉ reductionGroups π → css.getD i [] = [] := by
    intro i hi hn
    apply List.eq_nil_of_length_eq_zero
    rw [hsite i hi]
    simp only [groupSlots, hn, ↓reduceIte]
  have hglen : ∀ x : reductionGroups π,
      (colourList css x.val).length = if groupIsPair π r x.val then 2 else 1 := by
    intro x
    obtain ⟨h8, hpt⟩ := groupSite_spec _ (reductionGroups_template π x)
    rw [colourList, hsite _ h8, hpt]
    simp only [groupSlots, x.property, ↓reduceIte]
  have hgcol : ∀ x : reductionGroups π, ∀ c ∈ colourList css x.val, c < 4 :=
    fun x => hcol _ (groupSite_spec _ (reductionGroups_template π x)).1
  have hmono : monomialProduct 0 css = MvPolynomial.monomial
      (pauliExponent (reductionVectors π r) (colourLabel π r css)) 1 := by
    rw [monomialProduct_range, hl8, pauliMonomial_eq_prod, prod_tokens_eq_prod_groups]
    simp only [zero_add]
    rw [prod_sites_eq_prod_groups π _ (fun i hi hn => by rw [hnil i hi hn]; rfl)]
    apply Finset.prod_congr rfl
    intro x _
    rw [ringLeader_groupSite _ (reductionGroups_template π x)]
    exact vectorMonomial_group π r css x (hglen x) (hgcol x)
  rw [hmono, rationalSectorEntry_pauliMonomial]
  congr 1
  rw [formProduct_range, hl8]
  simp only [zero_add]
  rw [prod_sites_eq_prod_groups π _ (fun i hi hn => by
    rw [hnil i hi hn]; exact gaussianValue_one)]
  apply Finset.prod_congr rfl
  intro x _
  rw [(groupSite_spec _ (reductionGroups_template π x)).2]
  exact localForm_group π r ε css a.val b.val x (hglen x) (hgcol x)

end AKLT.W.H1C021
