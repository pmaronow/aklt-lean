import AKLT.Blueprint.H1.NodesSector

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs
open AKLT.Blueprint.H1

namespace AKLT.W.H1M033

lemma count_subtype_filter {α : Type} [DecidableEq α] (s : Finset α)
    (p : α → Prop) [DecidablePred p] :
    (Finset.univ.filter fun x : s => p x.val).card = (s.filter p).card := by
  classical
  change (s.attach.filter fun x => p x.val).card = _
  rw [Finset.filter_attach]
  simp

def intWeightPart (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (b : ExchangeBasis π r ε) (x : reductionGroups π) : ℤ :=
  if groupIsPair π r x.val then
    if π.statusAt x.val = .D ∧ ε x = false then 0 else 1 - (b x).val
  else -(b x).val

lemma weight_summand_decomp (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (b : ExchangeBasis π r ε) (x : reductionGroups π) :
    (if groupIsPair π r x.val then
      if π.statusAt x.val = .D ∧ ε x = false then 0 else 1 - ((b x).val : ℚ)
     else 1 / 2 - ((b x).val : ℚ)) =
      (if groupIsPair π r x.val then (0 : ℚ) else 1 / 2) +
        (intWeightPart π r ε b x : ℚ) := by
  by_cases hp : groupIsPair π r x.val = true
  · by_cases hd : π.statusAt x.val = .D ∧ ε x = false
    · simp [intWeightPart, hp, hd]
    · simp [intWeightPart, hp, hd]
  · have hp' : groupIsPair π r x.val = false := Bool.eq_false_of_not_eq_true hp
    simp [intWeightPart, hp']
    push_cast
    ring

lemma exchangeWeight_decomp (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (b : ExchangeBasis π r ε) :
    exchangeWeight π r ε b =
      (((reductionGroups π).filter fun x => !groupIsPair π r x).card : ℚ) / 2 +
        (∑ x : reductionGroups π, (intWeightPart π r ε b x : ℚ)) := by
  unfold exchangeWeight
  calc
    (∑ x : reductionGroups π,
        if groupIsPair π r x.val then
          if π.statusAt x.val = .D ∧ ε x = false then 0 else 1 - ((b x).val : ℚ)
        else 1 / 2 - ((b x).val : ℚ)) =
      ∑ x : reductionGroups π,
        ((if groupIsPair π r x.val then (0 : ℚ) else 1 / 2) +
          (intWeightPart π r ε b x : ℚ)) := by
            apply Finset.sum_congr rfl
            intro x hx
            exact weight_summand_decomp π r ε b x
    _ = (∑ x : reductionGroups π,
          (if groupIsPair π r x.val then (0 : ℚ) else 1 / 2)) +
        ∑ x : reductionGroups π, (intWeightPart π r ε b x : ℚ) := by
          rw [Finset.sum_add_distrib]
    _ = (((reductionGroups π).filter fun x => !groupIsPair π r x).card : ℚ) / 2 +
        ∑ x : reductionGroups π, (intWeightPart π r ε b x : ℚ) := by
          congr 1
          calc
            (∑ x : reductionGroups π,
                if groupIsPair π r x.val = true then (0 : ℚ) else 1 / 2) =
              ∑ x : reductionGroups π,
                if groupIsPair π r x.val = false then (1 / 2 : ℚ) else 0 := by
                  apply Finset.sum_congr rfl
                  intro x hx
                  cases h : groupIsPair π r x.val <;> simp [h]
            _ = (((reductionGroups π).filter fun x => !groupIsPair π r x).card : ℚ) / 2 := by
              change (∑ x ∈ (Finset.univ : Finset (reductionGroups π)),
                if groupIsPair π r x.val = false then (1 / 2 : ℚ) else 0) = _
              rw [← Finset.sum_filter]
              rw [Finset.sum_const]
              simp only [nsmul_eq_mul, mul_comm]
              change (1 / 2 : ℚ) *
                (Finset.univ.filter fun x : reductionGroups π =>
                  groupIsPair π r x.val = false).card = _
              have hc := count_subtype_filter (s := reductionGroups π)
                (p := fun x => groupIsPair π r x = false)
              rw [hc]
              simp only [Bool.not_eq_true_eq_eq_false]
              ring

lemma parity_offset (n : ℕ) :
    ∃ z : ℤ, (n : ℚ) / 2 = (if Even n then (0 : ℚ) else 1 / 2) + z := by
  by_cases he : Even n
  · rcases he with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    subst n
    simp
  · have ho : Odd n := Nat.not_even_iff_odd.mp he
    rcases ho with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    subst n
    simp
    push_cast
    ring_nf

lemma tokenZ_mulVec {J : Finset (Fin 20)} (j : J) (v : (J → Fin 2) → ℂ)
    (σ : J → Fin 2) :
    (tokenMatrix J j (pauli 3)).mulVec v σ =
      (if σ j = 0 then (1 : ℂ) else -1) * v σ := by
  classical
  rw [Matrix.mulVec_apply]
  unfold dotProduct
  rw [Finset.sum_eq_single σ]
  · have hcond : ∀ k : J, k ≠ j → σ k = σ k := by simp
    have hentry : pauli 3 (σ j) (σ j) = if σ j = 0 then (1 : ℂ) else -1 := by
      rcases Fin.eq_zero_or_eq_succ (σ j) with h0 | ⟨i, hi⟩
      · simp [h0, pauli]
      · have hi0 : i = 0 := Subsingleton.elim _ _
        subst i
        simp [hi, pauli]
    have hdiag : (tokenMatrix J j (pauli 3)).row σ σ =
        if σ j = 0 then (1 : ℂ) else -1 := by
      change tokenMatrix J j (pauli 3) σ σ = _
      unfold tokenMatrix
      simp [hcond, hentry]
    change (tokenMatrix J j (pauli 3)).row σ σ * v σ = _
    rw [hdiag]
  · intro τ hτ hτσ
    by_cases hs : σ j = τ j
    · have hcond : ¬ ∀ k : J, k ≠ j → σ k = τ k := by
        intro h
        have heq : σ = τ := by
          funext k
          by_cases hk : k = j
          · subst k
            exact hs
          · exact h k hk
        apply hτσ
        exact heq.symm
      have hzero : (tokenMatrix J j (pauli 3)).row σ τ = 0 := by
        change tokenMatrix J j (pauli 3) σ τ = 0
        unfold tokenMatrix
        split
        · rename_i htrue
          have heq : σ = τ := by
            funext k
            by_cases hk : k = j
            · subst k
              exact hs
            · exact htrue k hk
          exact False.elim (hτσ heq.symm)
        · rfl
      exact mul_eq_zero.mpr (Or.inl (by simpa using hzero))
    · have hentry : pauli 3 (σ j) (τ j) = 0 := by
        rcases Fin.eq_zero_or_eq_succ (σ j) with hσ0 | ⟨i, hσs⟩
        · rcases Fin.eq_zero_or_eq_succ (τ j) with hτ0 | ⟨k, hτs⟩
          · exact (hs (hσ0.trans hτ0.symm)).elim
          · have hk0 : k = 0 := Subsingleton.elim _ _
            subst k
            simp [hσ0, hτs, pauli]
        · have hi0 : i = 0 := Subsingleton.elim _ _
          subst i
          rcases Fin.eq_zero_or_eq_succ (τ j) with hτ0 | ⟨k, hτs⟩
          · simp [hσs, hτ0, pauli]
          · have hk0 : k = 0 := Subsingleton.elim _ _
            subst k
            exact (hs (hσs.trans hτs.symm)).elim
      have hzero : tokenMatrix J j (pauli 3) σ τ = 0 := by
        unfold tokenMatrix
        split <;> simp [hentry]
      change tokenMatrix J j (pauli 3) σ τ * v τ = 0
      simp [hzero]
  · intro h
    exact False.elim (h (Finset.mem_univ σ))

lemma spinZ_coord {J : Finset (Fin 20)} (ψ : TensorSpace J) (σ : J → Fin 2) :
    (totalSpinZ J ψ).ofLp σ =
      (∑ j : J, if σ j = 0 then (1 / 2 : ℂ) else -(1 / 2 : ℂ)) * ψ.ofLp σ := by
  classical
  change (((1 / 2 : ℂ) • ∑ j : J, tokenMatrix J j (pauli 3)).mulVec ψ.ofLp) σ = _
  rw [Matrix.smul_mulVec, Matrix.sum_mulVec]
  simp only [Pi.smul_apply, Finset.sum_apply]
  change (1 / 2 : ℂ) *
    (∑ j ∈ (Finset.univ : Finset J), (tokenMatrix J j (pauli 3)).mulVec ψ.ofLp σ) =
      (∑ j ∈ (Finset.univ : Finset J),
        if σ j = 0 then (1 / 2 : ℂ) else -(1 / 2 : ℂ)) * ψ.ofLp σ
  simp_rw [tokenZ_mulVec]
  rw [Finset.mul_sum]
  conv_rhs =>
    change (∑ j ∈ (Finset.univ : Finset J),
      (if σ j = 0 then (1 / 2 : ℂ) else -(1 / 2 : ℂ))) * ψ.ofLp σ
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : σ j = 0 <;> simp [h] <;> ring

def groupSlots (π : PatternData) (r : Representation) (x : Plane) : Finset (Fin 20) :=
  if groupIsPair π r x then {groupLeader x, groupSecond x} else {groupLeader x}

lemma reductionVectors_eq_groupSlots (π : PatternData) (r : Representation) :
    reductionVectors π r = (reductionGroups π).biUnion (groupSlots π r) := rfl

def spinTokenWeight (i : Fin 2) : ℚ := if i = 0 then 1 / 2 else -(1 / 2)

def potentialSlots (x : Plane) : Finset (Fin 20) := {groupLeader x, groupSecond x}

lemma groupLeader_ne_groupSecond (x : Plane) : groupLeader x ≠ groupSecond x := by
  have hl : (groupLeader x).val ≤ 17 := by
    unfold groupLeader
    split_ifs <;> omega
  intro h
  have hs : (groupSecond x).val = (groupLeader x).val + 1 := by
    simp [groupSecond, Nat.min_eq_right (by omega : (groupLeader x).val + 1 ≤ 19)]
  have hv := congrArg Fin.val h
  simp only [hs] at hv
  omega

lemma potentialSlots_disjoint (π : PatternData) (x y : Plane)
    (hx : x ∈ reductionGroups π) (hy : y ∈ reductionGroups π) (hxy : x ≠ y) :
    Disjoint (potentialSlots x) (potentialSlots y) := by
  classical
  have hxCases : x = (2, 0) ∨ x = (0, 2) ∨ x = (-2, 0) ∨ x = (1, 1) ∨
      x = (-1, 1) ∨ x = (-1, -1) ∨ x = (1, -1) ∨ x = (0, -2) := by
    have hm : x ∈ templateCorners ∪ templateTips := (Finset.mem_filter.mp hx).1
    simpa [templateCorners, templateTips] using hm
  have hyCases : y = (2, 0) ∨ y = (0, 2) ∨ y = (-2, 0) ∨ y = (1, 1) ∨
      y = (-1, 1) ∨ y = (-1, -1) ∨ y = (1, -1) ∨ y = (0, -2) := by
    have hm : y ∈ templateCorners ∪ templateTips := (Finset.mem_filter.mp hy).1
    simpa [templateCorners, templateTips] using hm
  rcases hxCases with h | h | h | h | h | h | h | h <;>
    rcases hyCases with hy | hy | hy | hy | hy | hy | hy | hy <;>
    subst x <;> subst y <;> simp_all [potentialSlots, groupLeader, groupSecond]

lemma groupSlots_pairwiseDisjoint (π : PatternData) (r : Representation) :
    ((reductionGroups π : Finset Plane) : Set Plane).PairwiseDisjoint (groupSlots π r) := by
  classical
  rw [Finset.pairwiseDisjoint_iff]
  intro x hx y hy hinter
  by_contra hxy
  have hd := potentialSlots_disjoint π x y hx hy hxy
  rcases hinter with ⟨j, hj⟩
  simp only [Finset.mem_inter] at hj
  have hleft : j ∈ potentialSlots x := by
    by_cases hp : groupIsPair π r x = true
    · simpa [groupSlots, potentialSlots, hp] using hj.1
    · have hp' : groupIsPair π r x = false := Bool.eq_false_of_not_eq_true hp
      have hjx := hj.1
      simp [groupSlots, hp'] at hjx
      simp only [potentialSlots, Finset.mem_insert, Finset.mem_singleton]
      exact Or.inl hjx
  have hright : j ∈ potentialSlots y := by
    by_cases hp : groupIsPair π r y = true
    · simpa [groupSlots, potentialSlots, hp] using hj.2
    · have hp' : groupIsPair π r y = false := Bool.eq_false_of_not_eq_true hp
      have hjy := hj.2
      simp [groupSlots, hp'] at hjy
      simp only [potentialSlots, Finset.mem_insert, Finset.mem_singleton]
      exact Or.inl hjy
  exact (Finset.disjoint_left.mp hd hleft) hright

lemma sum_subtype_eq_base {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (s : Finset α) (f : (x : s) → M) :
    (∑ x : s, f x) =
      ∑ x ∈ s, (if h : x ∈ s then f ⟨x, h⟩ else 0) := by
  classical
  let g : α → M := fun x => if h : x ∈ s then f ⟨x, h⟩ else 0
  have h := Finset.sum_attach s g
  simpa [g] using h

lemma groupSlot_mem_reductionVectors (π : PatternData) (r : Representation)
    (x : Plane) (hx : x ∈ reductionGroups π) (j : Fin 20)
    (hj : j ∈ groupSlots π r x) : j ∈ reductionVectors π r := by
  rw [reductionVectors_eq_groupSlots]
  exact Finset.mem_biUnion.mpr ⟨x, hx, hj⟩

def tokenWeightExt (π : PatternData) (r : Representation)
    (σ : reductionVectors π r → Fin 2) (j : Fin 20) : ℚ :=
  if h : j ∈ reductionVectors π r then spinTokenWeight (σ ⟨j, h⟩) else 0

lemma groupLeader_mem (π : PatternData) (r : Representation) (x : reductionGroups π) :
    groupLeader x.val ∈ reductionVectors π r := by
  unfold reductionVectors
  apply Finset.mem_biUnion.mpr
  refine ⟨x.val, x.property, ?_⟩
  by_cases hp : groupIsPair π r x.val = true <;> simp [hp]

lemma groupSecond_mem (π : PatternData) (r : Representation) (x : reductionGroups π)
    (h : groupIsPair π r x.val = true) : groupSecond x.val ∈ reductionVectors π r := by
  unfold reductionVectors
  apply Finset.mem_biUnion.mpr
  exact ⟨x.val, x.property, by simp [h]⟩

def groupSpinWeight (π : PatternData) (r : Representation)
    (x : reductionGroups π) (σ : reductionVectors π r → Fin 2) : ℚ :=
  if h : groupIsPair π r x.val = true then
    spinTokenWeight (σ ⟨groupLeader x.val, groupLeader_mem π r x⟩) +
      spinTokenWeight (σ ⟨groupSecond x.val, groupSecond_mem π r x h⟩)
  else spinTokenWeight (σ ⟨groupLeader x.val, groupLeader_mem π r x⟩)

def groupSpinWeightExt (π : PatternData) (r : Representation)
    (σ : reductionVectors π r → Fin 2) (x : Plane) : ℚ :=
  if h : x ∈ reductionGroups π then groupSpinWeight π r ⟨x, h⟩ σ else 0

lemma groupSlots_spinWeight_sum (π : PatternData) (r : Representation)
    (σ : reductionVectors π r → Fin 2) (x : Plane) (hx : x ∈ reductionGroups π) :
    (∑ j ∈ groupSlots π r x,
      tokenWeightExt π r σ j) = groupSpinWeight π r ⟨x, hx⟩ σ := by
  classical
  by_cases hp : groupIsPair π r x = true
  · have hne := groupLeader_ne_groupSecond x
    have hL : groupLeader x ∈ groupSlots π r x := by simp [groupSlots, hp]
    have hR : groupSecond x ∈ groupSlots π r x := by simp [groupSlots, hp]
    have hmemL := groupSlot_mem_reductionVectors π r x hx (groupLeader x) hL
    have hmemR := groupSlot_mem_reductionVectors π r x hx (groupSecond x) hR
    simp [groupSlots, groupSpinWeight, tokenWeightExt, spinTokenWeight,
      hp, hne, hmemL, hmemR, groupLeader_mem, groupSecond_mem]
  · have hp' : groupIsPair π r x = false := Bool.eq_false_of_not_eq_true hp
    have hL : groupLeader x ∈ groupSlots π r x := by simp [groupSlots, hp']
    have hmemL := groupSlot_mem_reductionVectors π r x hx (groupLeader x) hL
    simp [groupSlots, groupSpinWeight, tokenWeightExt, spinTokenWeight,
      hp', hmemL, groupLeader_mem]

def groupCoeff (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (b : ExchangeBasis π r ε) (x : reductionGroups π)
    (σ : reductionVectors π r → Fin 2) : ℤ :=
  let i := σ ⟨groupLeader x.val, groupLeader_mem π r x⟩
  if h : groupIsPair π r x.val = true then
    let j := σ ⟨groupSecond x.val, groupSecond_mem π r x h⟩
    if π.statusAt x.val = .D ∧ ε x = false then
      if i = 0 ∧ j = 1 then 1 else if i = 1 ∧ j = 0 then -1 else 0
    else if (b x).val = 0 then if i = 0 ∧ j = 0 then 1 else 0
    else if (b x).val = 1 then if i ≠ j then 1 else 0
    else if i = 1 ∧ j = 1 then 1 else 0
  else if i.val = (b x).val then 1 else 0

lemma exchangeBasisVector_eq_prod (π : PatternData) (r : Representation)
    (ε : ExchangeSigns π) (b : ExchangeBasis π r ε) (σ : reductionVectors π r → Fin 2) :
    exchangeBasisVector π r ε b σ = ∏ x : reductionGroups π, groupCoeff π r ε b x σ := by
  classical
  unfold exchangeBasisVector groupCoeff
  rfl

def groupWeightTerm (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (b : ExchangeBasis π r ε) (x : reductionGroups π) : ℚ :=
  if groupIsPair π r x.val then
    if π.statusAt x.val = .D ∧ ε x = false then 0 else 1 - ((b x).val : ℚ)
  else 1 / 2 - ((b x).val : ℚ)

def groupWeightTermExt (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (b : ExchangeBasis π r ε) (x : Plane) : ℚ :=
  if h : x ∈ reductionGroups π then groupWeightTerm π r ε b ⟨x, h⟩ else 0

lemma groupCoeff_support_weight (π : PatternData) (r : Representation)
    (ε : ExchangeSigns π) (b : ExchangeBasis π r ε) (x : reductionGroups π)
    (σ : reductionVectors π r → Fin 2) (hcoef : groupCoeff π r ε b x σ ≠ 0) :
    groupSpinWeight π r x σ = groupWeightTerm π r ε b x := by
  classical
  by_cases hp : groupIsPair π r x.val = true
  · let i := σ ⟨groupLeader x.val, groupLeader_mem π r x⟩
    let j := σ ⟨groupSecond x.val, groupSecond_mem π r x hp⟩
    have iCases : i = 0 ∨ i = 1 := by
      rcases Fin.eq_zero_or_eq_succ i with h0 | ⟨k, hk⟩
      · exact Or.inl h0
      · have hk0 : k = 0 := Subsingleton.elim _ _
        subst k
        exact Or.inr (by simpa using hk)
    have jCases : j = 0 ∨ j = 1 := by
      rcases Fin.eq_zero_or_eq_succ j with h0 | ⟨k, hk⟩
      · exact Or.inl h0
      · have hk0 : k = 0 := Subsingleton.elim _ _
        subst k
        exact Or.inr (by simpa using hk)
    by_cases hd : π.statusAt x.val = .D ∧ ε x = false
    · have hb : (b x).val = 0 := by
        have hlt : (b x).val < 1 := by
          simpa [GroupBasis, hp, hd] using (b x).isLt
        omega
      have hcoef' : (if i = 0 ∧ j = 1 then (1 : ℤ)
          else if i = 1 ∧ j = 0 then -1 else 0) ≠ 0 := by
        simpa [groupCoeff, hp, hd, i, j] using hcoef
      rcases iCases with hi0 | hi1 <;> rcases jCases with hj0 | hj1
      · simp [hi0, hj0] at hcoef'
      · simp [groupSpinWeight, groupWeightTerm, hp, hd, hb, i, j,
          spinTokenWeight, hi0, hj1] <;> norm_num
      · simp [groupSpinWeight, groupWeightTerm, hp, hd, hb, i, j,
          spinTokenWeight, hi1, hj0] <;> norm_num
      · simp [hi1, hj1] at hcoef'
    · have hlt : (b x).val < 3 := by
        simpa [GroupBasis, hp, hd] using (b x).isLt
      by_cases hb0 : (b x).val = 0
      · have hcoef' : (if i = 0 ∧ j = 0 then (1 : ℤ) else 0) ≠ 0 := by
          simpa [groupCoeff, hp, hd, hb0, i, j] using hcoef
        have hij : i = 0 ∧ j = 0 := by
          by_cases hh : i = 0 ∧ j = 0
          · exact hh
          · simp [hh] at hcoef'
        simp [groupSpinWeight, groupWeightTerm, hp, hd, hb0, i, j,
          spinTokenWeight, hij.1, hij.2] <;> norm_num
      · by_cases hb1 : (b x).val = 1
        · have hcoef' : (if i ≠ j then (1 : ℤ) else 0) ≠ 0 := by
            simpa [groupCoeff, hp, hd, hb0, hb1, i, j] using hcoef
          have hij : i ≠ j := by
            by_contra hh
            simp [hh] at hcoef'
          rcases iCases with hi0 | hi1 <;> rcases jCases with hj0 | hj1
          · exact (hij (hi0.trans hj0.symm)).elim
          · simp [groupSpinWeight, groupWeightTerm, hp, hd, hb0, hb1,
              i, j, spinTokenWeight, hi0, hj1] <;> norm_num
          · simp [groupSpinWeight, groupWeightTerm, hp, hd, hb0, hb1,
              i, j, spinTokenWeight, hi1, hj0] <;> norm_num
          · exact (hij (hi1.trans hj1.symm)).elim
        · have hb2 : (b x).val = 2 := by omega
          have hcoef' : (if i = 1 ∧ j = 1 then (1 : ℤ) else 0) ≠ 0 := by
            simpa [groupCoeff, hp, hd, hb0, hb1, hb2, i, j] using hcoef
          have hij : i = 1 ∧ j = 1 := by
            by_cases hh : i = 1 ∧ j = 1
            · exact hh
            · simp [hh] at hcoef'
          simp [groupSpinWeight, groupWeightTerm, hp, hd, hb0, hb1, hb2,
            i, j, spinTokenWeight, hij.1, hij.2] <;> norm_num
  · have hp' : groupIsPair π r x.val = false := Bool.eq_false_of_not_eq_true hp
    let i := σ ⟨groupLeader x.val, groupLeader_mem π r x⟩
    have hiVal : i.val = (b x).val := by
      have hc : (if i.val = (b x).val then (1 : ℤ) else 0) ≠ 0 := by
        simpa [groupCoeff, hp', i] using hcoef
      by_contra hn
      simp [hn] at hc
    by_cases hb0 : (b x).val = 0
    · have hi : i = 0 := Fin.ext (by simpa [hb0] using hiVal)
      simp [groupSpinWeight, groupWeightTerm, hp', hb0, i, hi,
        spinTokenWeight] <;> norm_num
    · have hb1 : (b x).val = 1 := by omega
      have hi : i = 1 := Fin.ext (by simpa [hb1] using hiVal)
      simp [groupSpinWeight, groupWeightTerm, hp', hb0, hb1, i, hi,
        spinTokenWeight] <;> norm_num

lemma groupWeightTerm_eq_intWeightPart (π : PatternData) (r : Representation)
    (ε : ExchangeSigns π) (b : ExchangeBasis π r ε) (x : reductionGroups π) :
    groupWeightTerm π r ε b x = (intWeightPart π r ε b x : ℚ) +
      (if groupIsPair π r x.val then (0 : ℚ) else 1 / 2) := by
  by_cases hp : groupIsPair π r x.val = true
  · simp [groupWeightTerm, intWeightPart, hp]
  · have hp' : groupIsPair π r x.val = false := Bool.eq_false_of_not_eq_true hp
    simp [groupWeightTerm, intWeightPart, hp']
    ring

lemma spinWeight_sum_eq_exchangeWeight_of_nonzero (π : PatternData) (r : Representation)
    (ε : ExchangeSigns π) (b : ExchangeBasis π r ε) (σ : reductionVectors π r → Fin 2)
    (hcoef : exchangeBasisVector π r ε b σ ≠ 0) :
    (∑ j : reductionVectors π r, spinTokenWeight (σ j)) = exchangeWeight π r ε b := by
  classical
  have hbase :
      (∑ j ∈ reductionVectors π r, tokenWeightExt π r σ j) =
      ∑ x ∈ reductionGroups π, groupSpinWeightExt π r σ x := by
    calc
      (∑ j ∈ reductionVectors π r, tokenWeightExt π r σ j) =
        ∑ j ∈ (reductionGroups π).biUnion (groupSlots π r), tokenWeightExt π r σ j := by
          rw [reductionVectors_eq_groupSlots]
      _ = ∑ x ∈ reductionGroups π,
          ∑ j ∈ groupSlots π r x, tokenWeightExt π r σ j := by
            rw [Finset.sum_biUnion (groupSlots_pairwiseDisjoint π r)]
      _ = ∑ x ∈ reductionGroups π, groupSpinWeightExt π r σ x := by
            apply Finset.sum_congr rfl
            intro x hx
            simpa [groupSpinWeightExt, hx] using groupSlots_spinWeight_sum π r σ x hx
  have hprod : ∏ x : reductionGroups π, groupCoeff π r ε b x σ ≠ 0 := by
    simpa [exchangeBasisVector_eq_prod] using hcoef
  have hcoeff : ∀ x : reductionGroups π, groupCoeff π r ε b x σ ≠ 0 := by
    have hp : ∀ x ∈ (Finset.univ : Finset (reductionGroups π)),
        groupCoeff π r ε b x σ ≠ 0 :=
      Finset.prod_ne_zero_iff.mp (by simpa using hprod)
    intro x
    exact hp x (Finset.mem_univ x)
  have hlocal : ∀ x : reductionGroups π,
      groupSpinWeight π r x σ = groupWeightTerm π r ε b x := by
    intro x
    exact groupCoeff_support_weight π r ε b x σ (hcoeff x)
  have hterms :
      (∑ x ∈ reductionGroups π, groupSpinWeightExt π r σ x) =
      ∑ x ∈ reductionGroups π, groupWeightTermExt π r ε b x := by
    apply Finset.sum_congr rfl
    intro x hx
    simp [groupSpinWeightExt, groupWeightTermExt, hx, hlocal ⟨x, hx⟩]
  have htermSum :
      (∑ x ∈ reductionGroups π, groupWeightTermExt π r ε b x) =
      exchangeWeight π r ε b := by
    calc
      (∑ x ∈ reductionGroups π, groupWeightTermExt π r ε b x) =
        ∑ x : reductionGroups π, groupWeightTerm π r ε b x := by
          symm
          simpa [groupWeightTermExt] using
            (sum_subtype_eq_base (reductionGroups π) (fun x => groupWeightTerm π r ε b x))
      _ = exchangeWeight π r ε b := by
          unfold exchangeWeight groupWeightTerm
          rfl
  calc
    (∑ j : reductionVectors π r, spinTokenWeight (σ j)) =
      ∑ j ∈ reductionVectors π r, tokenWeightExt π r σ j := by
        simpa [tokenWeightExt] using
          (sum_subtype_eq_base (reductionVectors π r) (fun j => spinTokenWeight (σ j)))
    _ = ∑ x ∈ reductionGroups π, groupSpinWeightExt π r σ x := hbase
    _ = ∑ x ∈ reductionGroups π, groupWeightTermExt π r ε b x := hterms
    _ = exchangeWeight π r ε b := htermSum

theorem main : AKLT.Blueprint.H1.SectorWeightBasisStatement := by
  intro π r ε b
  constructor
  · classical
    ext σ
    rw [spinZ_coord]
    by_cases hc : exchangeBasisVector π r ε b σ = 0
    · simp [sectorVector, hc]
    · have hwQ := spinWeight_sum_eq_exchangeWeight_of_nonzero π r ε b σ hc
      have hwC :
          (∑ j : reductionVectors π r, (spinTokenWeight (σ j) : ℂ)) =
            (exchangeWeight π r ε b : ℂ) := by
        exact_mod_cast hwQ
      have hw :
          (∑ j : reductionVectors π r,
            if σ j = 0 then (1 / 2 : ℂ) else -(1 / 2 : ℂ)) =
            (exchangeWeight π r ε b : ℂ) := by
        calc
          (∑ j : reductionVectors π r,
              if σ j = 0 then (1 / 2 : ℂ) else -(1 / 2 : ℂ)) =
            ∑ j : reductionVectors π r, (spinTokenWeight (σ j) : ℂ) := by
              apply Finset.sum_congr rfl
              intro j hj
              by_cases h : σ j = 0 <;> simp [spinTokenWeight, h]
          _ = (exchangeWeight π r ε b : ℂ) := hwC
      rw [hw]
      simp [sectorVector]
  · obtain ⟨z, hz⟩ := parity_offset
      ((reductionGroups π).filter fun x => !groupIsPair π r x).card
    refine ⟨z + ∑ x : reductionGroups π, intWeightPart π r ε b x, ?_⟩
    rw [exchangeWeight_decomp]
    unfold centralWeight
    rw [hz]
    push_cast
    ring

end AKLT.W.H1M033

#print axioms AKLT.W.H1M033.main
