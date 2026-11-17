module
public import AKLT.W.H1C006.Exchange

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.H1

namespace AKLT.W.H1C006

attribute [local instance] Classical.propDecidable

/-- The coordinate representative of a local single, symmetric pair, or
exterior pair basis element. -/
def firstBit (pair : Bool) (exterior : Prop) [Decidable exterior] (b : ℕ) : Fin 2 :=
  if pair then if exterior then 0 else if b = 2 then 1 else 0
  else if b = 0 then 0 else 1

def secondBit (pair : Bool) (exterior : Prop) [Decidable exterior] (b : ℕ) : Fin 2 :=
  if pair then if exterior then 1 else if b = 0 then 0 else 1
  else firstBit pair exterior b

def LocalCanonical (pair : Bool) (exterior : Prop) [Decidable exterior]
    (i j : Fin 2) : Prop :=
  if pair then if exterior then i = 0 ∧ j = 1 else ¬ (i = 1 ∧ j = 0) else True

def localCode (pair : Bool) (exterior : Prop) [Decidable exterior]
    (i j : Fin 2) : ℕ :=
  if pair then if exterior then 0 else i.val + j.val else i.val

theorem localCode_spec (pair : Bool) (exterior : Prop) [Decidable exterior]
    (i j : Fin 2) (h : LocalCanonical pair exterior i j) (hs : pair = false → j = i) :
    localCode pair exterior i j < H1M032.localDim pair exterior ∧
      firstBit pair exterior (localCode pair exterior i j) = i ∧
      secondBit pair exterior (localCode pair exterior i j) = j := by
  cases pair <;> by_cases he : exterior <;> fin_cases i <;> fin_cases j
  all_goals simp_all [LocalCanonical, localCode, firstBit, secondBit, H1M032.localDim]

theorem localVector_representative (pair : Bool) (exterior : Prop) [Decidable exterior]
    (b c : ℕ) (hb : b < H1M032.localDim pair exterior)
    (hc : c < H1M032.localDim pair exterior) :
    H1M032.localVector pair exterior c (firstBit pair exterior b)
      (secondBit pair exterior b) = if c = b then 1 else 0 := by
  have hd : H1M032.localDim pair exterior ≤ 3 := by
    cases pair <;> by_cases he : exterior <;> simp [H1M032.localDim, he]
  have hb' : b ≤ 2 := by omega
  have hc' : c ≤ 2 := by omega
  interval_cases b <;> interval_cases c <;> cases pair <;> by_cases he : exterior
  all_goals simp_all [H1M032.localDim, H1M032.localVector, firstBit, secondBit]

theorem token_has_owner (π : PatternData) (r : Representation) (j : reductionVectors π r) :
    ∃ x : reductionGroups π, j ∈ H1M032.groupSlots π r x := by
  have hj : j ∈ Finset.univ.biUnion (H1M032.groupSlots π r) := by
    rw [H1M032.groupSlots_cover]
    exact Finset.mem_univ j
  simpa only [Finset.mem_biUnion, Finset.mem_univ, true_and] using hj

/-- The disjoint group partition gives an owner to each tensor token. -/
def tokenOwner (π : PatternData) (r : Representation) (j : reductionVectors π r) :
    reductionGroups π :=
  Classical.choose (token_has_owner π r j)

theorem tokenOwner_mem (π : PatternData) (r : Representation) (j : reductionVectors π r) :
    j ∈ H1M032.groupSlots π r (tokenOwner π r j) := by
  exact Classical.choose_spec (token_has_owner π r j)

theorem tokenOwner_eq (π : PatternData) (r : Representation)
    (x : reductionGroups π) (j : reductionVectors π r) (hj : j ∈ H1M032.groupSlots π r x) :
    tokenOwner π r j = x := by
  classical
  by_contra hn
  have hd := H1M032.groupSlots_disjoint π r
    (Finset.mem_univ (tokenOwner π r j)) (Finset.mem_univ x) hn
  exact Finset.disjoint_left.mp hd (tokenOwner_mem π r j) hj

def basisConfiguration (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (b : ExchangeBasis π r ε) : reductionVectors π r → Fin 2 :=
  fun j =>
    let x := tokenOwner π r j
    if j = leaderToken π r x then
      firstBit (groupIsPair π r x.val) (π.statusAt x.val = .D ∧ ε x = false) (b x).val
    else secondBit (groupIsPair π r x.val) (π.statusAt x.val = .D ∧ ε x = false) (b x).val

theorem basisConfiguration_leader (π : PatternData) (r : Representation)
    (ε : ExchangeSigns π) (b : ExchangeBasis π r ε) (x : reductionGroups π) :
    basisConfiguration π r ε b (leaderToken π r x) =
      firstBit (groupIsPair π r x.val) (π.statusAt x.val = .D ∧ ε x = false) (b x).val := by
  classical
  unfold basisConfiguration
  rw [tokenOwner_eq π r x _ (H1M032.leader_mem_groupSlots π r x), if_pos rfl]

theorem basisConfiguration_second (π : PatternData) (r : Representation)
    (ε : ExchangeSigns π) (b : ExchangeBasis π r ε) (x : reductionGroups π) :
    basisConfiguration π r ε b (H1M032.secondOrLeader π r x) =
      secondBit (groupIsPair π r x.val) (π.statusAt x.val = .D ∧ ε x = false) (b x).val := by
  classical
  unfold basisConfiguration
  rw [tokenOwner_eq π r x _ (H1M032.second_mem_groupSlots π r x)]
  by_cases hp : groupIsPair π r x.val = true
  · rw [if_neg (H1M032.pair_tokens_ne π r x hp).symm]
  · have ht : H1M032.secondOrLeader π r x = leaderToken π r x := dif_neg hp
    rw [ht, if_pos rfl]
    simp only [secondBit, hp, Bool.false_eq_true, ↓reduceIte]

theorem groupVector_basisConfiguration (π : PatternData) (r : Representation)
    (ε : ExchangeSigns π) (b c : ExchangeBasis π r ε) (x : reductionGroups π) :
    H1M032.groupVector π r ε x (c x) (basisConfiguration π r ε b) =
      if c x = b x then 1 else 0 := by
  classical
  rw [H1M032.groupVector, basisConfiguration_leader, basisConfiguration_second]
  have h := localVector_representative (groupIsPair π r x.val)
    (π.statusAt x.val = .D ∧ ε x = false) (b x).val (c x).val (b x).isLt (c x).isLt
  rw [h]
  by_cases hcb : c x = b x
  · rw [hcb]
    simp only [ite_true, Int.cast_one]
  · have hval : (c x).val ≠ (b x).val := fun hv => hcb (Fin.ext hv)
    simp only [ite_eq_right hcb, ite_eq_right hval, Int.cast_zero]

theorem sectorVector_basisConfiguration (π : PatternData) (r : Representation)
    (ε : ExchangeSigns π) (b c : ExchangeBasis π r ε) :
    sectorVector π r ε c (basisConfiguration π r ε b) = if c = b then 1 else 0 := by
  classical
  rw [H1M032.sectorVector_eq_tensorGenerator]
  change (∏ x, H1M032.groupVector π r ε x (c x) (basisConfiguration π r ε b)) = _
  simp_rw [groupVector_basisConfiguration]
  by_cases h : c = b
  · subst c
    simp only [ite_true, Finset.prod_const_one]
  · rw [if_neg h]
    obtain ⟨x, hx⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ x) (if_neg hx)

def CanonicalAt (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (σ : reductionVectors π r → Fin 2) (x : reductionGroups π) : Prop :=
  LocalCanonical (groupIsPair π r x.val) (π.statusAt x.val = .D ∧ ε x = false)
    (σ (leaderToken π r x)) (σ (H1M032.secondOrLeader π r x))

theorem canonical_configuration (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (σ : reductionVectors π r → Fin 2) (hσ : ∀ x, CanonicalAt π r ε σ x) :
    ∃ b : ExchangeBasis π r ε, basisConfiguration π r ε b = σ := by
  classical
  have hs (x : reductionGroups π) : groupIsPair π r x.val = false →
      σ (H1M032.secondOrLeader π r x) = σ (leaderToken π r x) := by
    intro hp
    have ht : H1M032.secondOrLeader π r x = leaderToken π r x := by
      exact dif_neg (by rw [hp]; decide)
    exact congrArg σ ht
  have hcode (x : reductionGroups π) := localCode_spec (groupIsPair π r x.val)
    (π.statusAt x.val = .D ∧ ε x = false) (σ (leaderToken π r x))
    (σ (H1M032.secondOrLeader π r x)) (hσ x) (hs x)
  let b : ExchangeBasis π r ε := fun x => ⟨_, (hcode x).1⟩
  refine ⟨b, ?_⟩
  funext j
  let x := tokenOwner π r j
  have hj := tokenOwner_mem π r j
  change j ∈ H1M032.groupSlots π r x at hj
  by_cases hp : groupIsPair π r x.val = true
  · simp only [H1M032.groupSlots, hp, ↓reduceIte, Finset.mem_insert,
      Finset.mem_singleton] at hj
    rcases hj with hj | hj
    · calc
        basisConfiguration π r ε b j =
            basisConfiguration π r ε b (leaderToken π r x) := congrArg _ hj
        _ = σ (leaderToken π r x) :=
          (basisConfiguration_leader π r ε b x).trans (hcode x).2.1
        _ = σ j := congrArg σ hj.symm
    · calc
        basisConfiguration π r ε b j =
            basisConfiguration π r ε b (H1M032.secondOrLeader π r x) := congrArg _ hj
        _ = σ (H1M032.secondOrLeader π r x) :=
          (basisConfiguration_second π r ε b x).trans (hcode x).2.2
        _ = σ j := congrArg σ hj.symm
  · simp only [H1M032.groupSlots, hp, Bool.false_eq_true, ↓reduceIte,
      Finset.mem_singleton] at hj
    calc
      basisConfiguration π r ε b j =
          basisConfiguration π r ε b (leaderToken π r x) := congrArg _ hj
      _ = σ (leaderToken π r x) :=
        (basisConfiguration_leader π r ε b x).trans (hcode x).2.1
      _ = σ j := congrArg σ hj.symm

end AKLT.W.H1C006
