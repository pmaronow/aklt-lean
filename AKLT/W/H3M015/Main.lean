import AKLT.Blueprint.H3.NodesDomination

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.H3M015

private def rewardPairCoefficient (outgoingSite : Plane) (live : Finset Plane)
    (straight : Bool) (p : Finset Plane) : ℚ :=
  if outgoingSite ∈ p then
    if live.card = 1 then betaPrimeBound straight else betaBound straight
  else alphaBound straight

private def rewardPairTerm (outgoingSite : Plane) (live : Finset Plane)
    (straight : Bool) (p : Finset Plane) : ℚ :=
  rewardPairCoefficient outgoingSite live straight p * kernelWitness (responsePairType p)

private theorem betaPrimeBound_le_betaBound (straight : Bool) :
    betaPrimeBound straight ≤ betaBound straight := by
  cases straight <;> norm_num [betaPrimeBound, betaBound]

private theorem rewardPairCoefficient_mono
    (outgoingSite : Plane) {live₂ live₁ : Finset Plane}
    (hlive : live₂ ⊆ live₁) (straight : Bool) (p : Finset Plane)
    (hp : p ⊆ insert outgoingSite live₂) (hcard : p.card = 2)
    (hout : outgoingSite ∈ p) :
    rewardPairCoefficient outgoingSite live₂ straight p ≤
      rewardPairCoefficient outgoingSite live₁ straight p := by
  have hnonempty : live₂.Nonempty := by
    by_contra h
    have hempty : live₂ = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hp' : p ⊆ ({outgoingSite} : Finset Plane) := by
      simpa [hempty] using hp
    have hle : p.card ≤ ({outgoingSite} : Finset Plane).card := Finset.card_le_card hp'
    simp at hle
    omega
  have hcardle : live₂.card ≤ live₁.card := Finset.card_le_card hlive
  have hcard_of_one : live₁.card = 1 → live₂.card = 1 := by
    intro h₁
    have hpos : 0 < live₂.card := Finset.card_pos.mpr hnonempty
    omega
  unfold rewardPairCoefficient
  simp only [ite_eq_left hout]
  by_cases h₂ : live₂.card = 1
  · by_cases h₁ : live₁.card = 1
    · simp [h₂, h₁]
    · simp [h₂, h₁]
      exact betaPrimeBound_le_betaBound straight
  · by_cases h₁ : live₁.card = 1
    · exact (h₂ (hcard_of_one h₁)).elim
    · simp [h₂, h₁]

private theorem rewardPairTerm_mono
    (outgoingSite : Plane) {live₂ live₁ : Finset Plane}
    (hlive : live₂ ⊆ live₁) (straight : Bool) (p : Finset Plane)
    (hp : p ⊆ insert outgoingSite live₂) (hcard : p.card = 2) :
    rewardPairTerm outgoingSite live₂ straight p ≤
      rewardPairTerm outgoingSite live₁ straight p := by
  unfold rewardPairTerm
  by_cases hout : outgoingSite ∈ p
  · apply mul_le_mul_of_nonneg_right
        (rewardPairCoefficient_mono outgoingSite hlive straight p hp hcard hout)
    cases responsePairType p <;> norm_num [kernelWitness]
  · simp [rewardPairCoefficient, hout]

private theorem rewardPairTerm_nonneg
    (outgoingSite : Plane) (live : Finset Plane) (straight : Bool) (p : Finset Plane) :
    0 ≤ rewardPairTerm outgoingSite live straight p := by
  unfold rewardPairTerm rewardPairCoefficient
  apply mul_nonneg
  · split_ifs <;> cases straight <;> norm_num [alphaBound, betaBound, betaPrimeBound]
  · cases responsePairType p <;> norm_num [kernelWitness]

theorem main : AKLT.Blueprint.H3.RewardForgettingStatement := by
  intro x incoming outgoing _ dead₁ dead₂ hdead
  classical
  let outgoingSite := x + outgoing.step
  let base := (neighbours x).erase (x - incoming.step) |>.erase outgoingSite
  let live₁ := base \ dead₁
  let live₂ := base \ dead₂
  have hlive : live₂ ⊆ live₁ := by
    intro z hz
    simp only [live₂, live₁, Finset.mem_sdiff] at hz ⊢
    exact ⟨hz.1, fun h => hz.2 (hdead h)⟩
  have hpairs : (insert outgoingSite live₂).powersetCard 2 ⊆
      (insert outgoingSite live₁).powersetCard 2 :=
    Finset.powersetCard_mono (Finset.insert_subset_insert outgoingSite hlive)
  change (∑ p ∈ (insert outgoingSite live₂).powersetCard 2,
      rewardPairTerm outgoingSite live₂ (decide (outgoing = incoming)) p) ≤
    ∑ p ∈ (insert outgoingSite live₁).powersetCard 2,
      rewardPairTerm outgoingSite live₁ (decide (outgoing = incoming)) p
  calc
    (∑ p ∈ (insert outgoingSite live₂).powersetCard 2,
        rewardPairTerm outgoingSite live₂ (decide (outgoing = incoming)) p) ≤
      ∑ p ∈ (insert outgoingSite live₂).powersetCard 2,
        rewardPairTerm outgoingSite live₁ (decide (outgoing = incoming)) p := by
          apply Finset.sum_le_sum
          intro p hp
          have hp' : p ⊆ insert outgoingSite live₂ := (Finset.mem_powersetCard.mp hp).1
          have hcard : p.card = 2 := (Finset.mem_powersetCard.mp hp).2
          exact rewardPairTerm_mono outgoingSite hlive (decide (outgoing = incoming)) p hp' hcard
    _ ≤ ∑ p ∈ (insert outgoingSite live₁).powersetCard 2,
        rewardPairTerm outgoingSite live₁ (decide (outgoing = incoming)) p := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hpairs
          intro p hp _
          exact rewardPairTerm_nonneg outgoingSite live₁ (decide (outgoing = incoming)) p

end AKLT.W.H3M015
