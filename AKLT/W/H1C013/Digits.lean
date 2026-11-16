import AKLT.W.H1C013.Model

noncomputable section
open scoped BigOperators

namespace AKLT.W.H1C013
open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

def digitBit (π : PatternData) (r : Representation) (f : Nat → Nat) (i : Nat) : Nat :=
  if groupIsPair π r (groupPoint i) = true ∧ π.statusAt (groupPoint i) = .D ∧ f i = 3
  then 1 else 0

theorem digitBit_lt (π : PatternData) (r : Representation) (f : Nat → Nat) (i : Nat) :
    digitBit π r f i < 2 := by unfold digitBit; split_ifs <;> omega

theorem parity_radix (π : PatternData) (r : Representation) (ε : ExchangeSigns π) :
    exchangeParity π r ε = radix (activePositions π) (fun _ => 2)
      (fun i => if exterior π r ε i then 1 else 0) := by
  classical
  unfold exchangeParity radix activePositions
  rw [List.foldl_filter]
  apply foldl_congr_mem
  intro a i hi
  by_cases hx : groupPoint i ∈ reductionGroups π <;>
    simp [exterior, hx, Nat.mul_comm]

theorem bit_fullDigit (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (b : ExchangeBasis π r ε) (i : Nat) :
    digitBit π r (fullDigit π r ε b) i = if exterior π r ε i then 1 else 0 := by
  classical
  by_cases hx : groupPoint i ∈ reductionGroups π
  · have hb := (b ⟨_,hx⟩).isLt
    change (b ⟨_,hx⟩).val <
      (if groupIsPair π r (groupPoint i) then
        if π.statusAt (groupPoint i) = .D ∧ ε ⟨_,hx⟩ = false then 1 else 3 else 2) at hb
    cases hp : groupIsPair π r (groupPoint i) <;>
      by_cases hd : π.statusAt (groupPoint i) = .D <;>
      by_cases he : ε ⟨_,hx⟩ = false <;>
      simp [digitBit, fullDigit, exterior, hx, hp, hd, he] at hb ⊢ <;> omega
  · simp [digitBit, fullDigit, exterior, hx]

theorem coordinate_lt (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (f : Nat → Nat) (hf : ∀ i ∈ positions, f i < groupDim π r (groupPoint i))
    (hbit : ∀ i ∈ activePositions π,
      digitBit π r f i = if exterior π r ε i then 1 else 0)
    (x : reductionGroups π) :
    (if exterior π r ε (groupPosition π x) then 0 else f (groupPosition π x)) <
      (if groupIsPair π r x.val then
        if π.statusAt x.val = .D ∧ ε x = false then 1 else 3 else 2) := by
  classical
  let i := groupPosition π x
  have hi : i ∈ positions := by simpa [positions] using groupPosition_lt π x
  have hx : groupPoint i = x.val := groupPosition_point π x
  have hm : groupPoint i ∈ reductionGroups π := hx ▸ x.property
  have hdim := hf i hi
  have hbits := hbit i ((mem_activePositions π i).mpr ⟨groupPosition_lt π x, hm⟩)
  change (if exterior π r ε i then 0 else f i) < _
  cases hp : groupIsPair π r x.val <;>
    by_cases hd : π.statusAt x.val = .D <;>
    by_cases he : ε x = false <;>
    simp [exterior, digitBit, groupDim, groupSlots, hm, hx, hp, hd, he] at hdim hbits ⊢ <;>
    omega

/-- A full digit string in the selected exchange sector is exactly one
exchange-basis coordinate string. The exterior local coordinate is zero,
while its full coordinate is three. -/
theorem basis_of_digits (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (f : Nat → Nat) (hf : ∀ i ∈ positions, f i < groupDim π r (groupPoint i))
    (hbit : ∀ i ∈ activePositions π,
      digitBit π r f i = if exterior π r ε i then 1 else 0) :
    ∃ b : ExchangeBasis π r ε, ∀ i ∈ positions, fullDigit π r ε b i = f i := by
  classical
  let b : ExchangeBasis π r ε := fun x =>
    ⟨if exterior π r ε (groupPosition π x) then 0 else f (groupPosition π x),
      coordinate_lt π r ε f hf hbit x⟩
  refine ⟨b, ?_⟩
  intro i hi
  have hi' : i < 8 := by simpa [positions] using hi
  by_cases hx : groupPoint i ∈ reductionGroups π
  · have hpos := groupPosition_unique π ⟨_,hx⟩ i hi' rfl
    by_cases he : exterior π r ε i = true
    · have hb := hbit i ((mem_activePositions π i).mpr ⟨hi',hx⟩)
      have hd : f i = 3 := by
        simp only [he, ↓reduceIte, digitBit] at hb
        split_ifs at hb with hb'
        exact hb'.2.2
      simp only [fullDigit, dif_pos hx, he, ↓reduceIte, hd]
    · have he' : exterior π r ε i = false := Bool.eq_false_iff.mpr he
      simp only [fullDigit, dif_pos hx, he', Bool.false_eq_true, ↓reduceIte,
        b, hpos, Fin.val_mk]
  · have hf' := hf i hi
    simp [groupDim, groupSlots, hx] at hf'
    simp [fullDigit, hx, show f i = 0 by omega]

def digitWeight (π : PatternData) (r : Representation) (f : Nat → Nat) (i : Nat) : Int :=
  if groupPoint i ∈ reductionGroups π then
    if groupIsPair π r (groupPoint i) then if f i = 3 then 0 else 2 - 2*(f i : Int)
    else 1 - 2*(f i : Int)
  else 0

theorem weight_fullDigit (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (b : ExchangeBasis π r ε) :
    (((positions.map (digitWeight π r (fullDigit π r ε b))).sum : Int) : ℚ) =
      2 * exchangeWeight π r ε b := by
  classical
  let w := fun x : reductionGroups π =>
    if groupIsPair π r x.val then
      if π.statusAt x.val = .D ∧ ε x = false then 0 else 1 - ((b x).val : ℚ)
    else 1/2 - ((b x).val : ℚ)
  have hloc (i : Nat) :
      (digitWeight π r (fullDigit π r ε b) i : ℚ) =
        if h : groupPoint i ∈ reductionGroups π then 2 * w ⟨_,h⟩ else 0 := by
    by_cases hx : groupPoint i ∈ reductionGroups π
    · have hb := (b ⟨_,hx⟩).isLt
      change (b ⟨_,hx⟩).val <
        (if groupIsPair π r (groupPoint i) then
          if π.statusAt (groupPoint i) = .D ∧ ε ⟨_,hx⟩ = false then 1 else 3 else 2) at hb
      cases hp : groupIsPair π r (groupPoint i) <;>
        by_cases hd : π.statusAt (groupPoint i) = .D <;>
        by_cases he : ε ⟨_,hx⟩ = false <;>
        simp [digitWeight, fullDigit, exterior, w, hx, hp, hd, he] at hb ⊢
      all_goals
        have hn : (b ⟨_,hx⟩).val ≠ 3 := by omega
        try simp only [hn, ↓reduceIte]
        push_cast
        norm_num
        ring
    · simp [digitWeight, hx]
  rw [Int.cast_list_sum, List.map_map]
  calc
    _ = (positions.map (fun i => if h : groupPoint i ∈ reductionGroups π then
        2 * w ⟨_,h⟩ else 0)).sum := by
      congr 1
      apply List.map_congr_left
      intro i hi
      exact hloc i
    _ = ∑ x : reductionGroups π, 2 * w x := sum_positions π (fun x => 2*w x)
    _ = 2 * exchangeWeight π r ε b := by
      change (∑ x : reductionGroups π, 2 * w x) = 2 * ∑ x : reductionGroups π, w x
      rw [Finset.mul_sum]

theorem single_count (π : PatternData) (r : Representation) :
    (positions.filter (fun i => groupSlots π r (groupPoint i) == 1)).length =
      ((reductionGroups π).filter fun x => !groupIsPair π r x).card := by
  classical
  rw [length_filter_sum]
  have he : (positions.map (fun i => if groupSlots π r (groupPoint i) == 1 then 1 else 0)).sum =
      (positions.map (fun i => if h : groupPoint i ∈ reductionGroups π then
        (if groupIsPair π r (groupPoint i) then 0 else 1 : Nat) else 0)).sum := by
    congr 1
    apply List.map_congr_left
    intro i hi
    by_cases hx : groupPoint i ∈ reductionGroups π <;>
      cases hp : groupIsPair π r (groupPoint i) <;> simp [groupSlots, hx, hp]
  rw [he, sum_positions π (fun x => if groupIsPair π r x.val then (0 : Nat) else 1)]
  calc
    _ = ∑ x ∈ reductionGroups π, if groupIsPair π r x then (0 : Nat) else 1 :=
      Finset.sum_attach _ _
    _ = _ := by
      rw [Finset.card_filter]
      apply Finset.sum_congr rfl
      intro x hx
      cases hp : groupIsPair π r x <;> simp [hp]

end AKLT.W.H1C013
