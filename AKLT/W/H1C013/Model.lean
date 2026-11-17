module
public import AKLT.W.H1C013.Radix

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators

namespace AKLT.W.H1C013

open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

def positions : List Nat := List.range 8

theorem group_points : (positions.map groupPoint).toFinset = templateCorners ∪ templateTips := by
  norm_num [positions, groupPoint, ringSites, List.range_succ,
    templateCorners, templateTips, Finset.ext_iff]
  tauto

theorem groupPoint_injective {i j : Nat} (hi : i < 8) (hj : j < 8)
    (h : groupPoint i = groupPoint j) : i = j := by
  interval_cases i <;> interval_cases j <;>
    first | rfl | norm_num [groupPoint, ringSites] at h

theorem group_occurs (π : PatternData) (x : reductionGroups π) :
    ∃ i : Nat, i < 8 ∧ groupPoint i = x.val := by
  have hm : x.val ∈ (positions.map groupPoint).toFinset := by
    rw [group_points]
    exact (Finset.mem_filter.mp x.property).1
  simpa only [List.mem_toFinset, List.mem_map, positions, List.mem_range] using hm

def groupPosition (π : PatternData) (x : reductionGroups π) : Nat :=
  Classical.choose (group_occurs π x)

theorem groupPosition_lt (π : PatternData) (x : reductionGroups π) :
    groupPosition π x < 8 := (Classical.choose_spec (group_occurs π x)).1

theorem groupPosition_point (π : PatternData) (x : reductionGroups π) :
    groupPoint (groupPosition π x) = x.val := (Classical.choose_spec (group_occurs π x)).2

theorem groupPosition_unique (π : PatternData) (x : reductionGroups π) (i : Nat)
    (hi : i < 8) (hx : groupPoint i = x.val) : groupPosition π x = i :=
  groupPoint_injective (groupPosition_lt π x) hi ((groupPosition_point π x).trans hx.symm)

def activePositions (π : PatternData) : List Nat :=
  positions.filter fun i => decide (groupPoint i ∈ reductionGroups π)

theorem mem_activePositions (π : PatternData) (i : Nat) :
    i ∈ activePositions π ↔ i < 8 ∧ groupPoint i ∈ reductionGroups π := by
  simp [activePositions, positions]

theorem sum_groups {M : Type*} [AddCommMonoid M] (π : PatternData)
    (f : reductionGroups π → M) :
    ((activePositions π).attach.map (fun i =>
      f ⟨groupPoint i.val, ((mem_activePositions π i.val).mp i.property).2⟩)).sum =
      ∑ x : reductionGroups π, f x := by
  classical
  have hn : (activePositions π).Nodup := List.nodup_range.filter _
  rw [← List.sum_toFinset _ hn.attach]
  apply Finset.sum_bij (fun i _ =>
      (⟨groupPoint i.val, ((mem_activePositions π i.val).mp i.property).2⟩ : reductionGroups π))
  · intros; exact Finset.mem_univ _
  · intro i hi j hj he
    apply Subtype.ext
    apply groupPoint_injective ((mem_activePositions π _).mp i.property).1
      ((mem_activePositions π _).mp j.property).1
    exact congrArg Subtype.val he
  · intro x hx
    let i : { i // i ∈ activePositions π } :=
      ⟨groupPosition π x, (mem_activePositions π _).mpr
        ⟨groupPosition_lt π x, (groupPosition_point π x) ▸ x.property⟩⟩
    refine ⟨i, by simp, ?_⟩
    exact Subtype.ext (groupPosition_point π x)
  · intros; rfl

def exterior (π : PatternData) (r : Representation) (ε : ExchangeSigns π) (i : Nat) : Bool :=
  if h : groupPoint i ∈ reductionGroups π then
    groupIsPair π r (groupPoint i) && decide (π.statusAt (groupPoint i) = .D ∧ ε ⟨_,h⟩ = false)
  else false

theorem sum_positions {M : Type*} [AddCommMonoid M] (π : PatternData)
    (f : reductionGroups π → M) :
    (positions.map (fun i => if h : groupPoint i ∈ reductionGroups π then
      f ⟨_,h⟩ else 0)).sum = ∑ x : reductionGroups π, f x := by
  classical
  rw [sum_filter_zero positions (fun i => decide (groupPoint i ∈ reductionGroups π))
    _ (by intro i hi hn; simp only [decide_eq_false_iff_not] at hn; simp [hn])]
  rw [← sum_groups π f]
  change ((activePositions π).map _).sum = _
  rw [← List.attach_map_val (l := activePositions π)]
  congr 1
  apply List.map_congr_left
  intro i hi
  simp only [Function.comp_apply,
    dif_pos ((mem_activePositions π i.val).mp i.property).2]

def fullDigit (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (b : ExchangeBasis π r ε) (i : Nat) : Nat :=
  if h : groupPoint i ∈ reductionGroups π then
    if exterior π r ε i then 3 else (b ⟨_,h⟩).val
  else 0

theorem fullDigit_lt (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (b : ExchangeBasis π r ε) (i : Nat) :
    fullDigit π r ε b i < groupDim π r (groupPoint i) := by
  classical
  by_cases hx : groupPoint i ∈ reductionGroups π
  · have hb := (b ⟨_,hx⟩).isLt
    change (b ⟨_,hx⟩).val <
      (if groupIsPair π r (groupPoint i) then
        if π.statusAt (groupPoint i) = .D ∧ ε ⟨_,hx⟩ = false then 1 else 3 else 2) at hb
    cases hp : groupIsPair π r (groupPoint i) <;>
      by_cases hd : π.statusAt (groupPoint i) = .D <;>
      by_cases he : ε ⟨_,hx⟩ = false <;>
      simp [fullDigit, exterior, groupDim, groupSlots, hx, hp, hd, he] at hb ⊢ <;> omega
  · simp [fullDigit, groupDim, groupSlots, hx]

theorem groupDim_pos (π : PatternData) (r : Representation) (i : Nat) :
    0 < groupDim π r (groupPoint i) := by
  unfold groupDim
  split_ifs <;> omega

theorem basisCode_radix (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (b : ExchangeBasis π r ε) :
    exchangeBasisCode π r ε b = radix positions
      (fun i => groupDim π r (groupPoint i)) (fullDigit π r ε b) := by
  unfold exchangeBasisCode radix
  apply foldl_congr_mem
  intro a i hi
  by_cases hx : groupPoint i ∈ reductionGroups π <;>
    simp [fullDigit, exterior, hx]

theorem basisCode_injective (π : PatternData) (r : Representation) (ε : ExchangeSigns π) :
    Function.Injective (exchangeBasisCode π r ε) := by
  intro b b' he
  rw [basisCode_radix, basisCode_radix] at he
  have hd := radix_injective positions (fun i => groupDim π r (groupPoint i))
    (fullDigit π r ε b) (fullDigit π r ε b')
    (fun i _ => fullDigit_lt π r ε b i) (fun i _ => fullDigit_lt π r ε b' i) he
  funext x
  apply Fin.ext
  let i := groupPosition π x
  have hi : i ∈ positions := by simpa [positions] using groupPosition_lt π x
  have hx : groupPoint i = x.val := groupPosition_point π x
  have hm : groupPoint i ∈ reductionGroups π := hx ▸ x.property
  have hval := hd i hi
  by_cases hext : exterior π r ε i = true
  · have hb := (b x).isLt
    have hb' := (b' x).isLt
    have hext' : groupIsPair π r x.val = true ∧ π.statusAt x.val = .D ∧ ε x = false := by
      simpa [exterior, hm, hx] using hext
    simp only [GroupBasis, hext'.1, hext'.2.1, hext'.2.2, and_self,
      ↓reduceIte] at hb hb'
    omega
  · have hext' : exterior π r ε i = false := Bool.eq_false_iff.mpr hext
    have hsub : (⟨groupPoint i, hm⟩ : reductionGroups π) = x := Subtype.ext hx
    have hv : (b ⟨_,hm⟩).val = (b' ⟨_,hm⟩).val := by
      simpa only [fullDigit, dif_pos hm, hext', Bool.false_eq_true, ↓reduceIte] using hval
    exact (congrArg (fun y => (b y).val) hsub).symm.trans
      (hv.trans (congrArg (fun y => (b' y).val) hsub))

end AKLT.W.H1C013
