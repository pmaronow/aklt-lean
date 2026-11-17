module
public import AKLT.Blueprint.H3.NodesCertificate

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.H3M020

private def tr (t : Plane) (z : Plane) : Plane := z + t

private theorem tr_inj (t : Plane) : Function.Injective (tr t) := by
  intro x y h
  dsimp [tr] at h
  exact add_right_cancel h

private theorem responsePairType_image_tr (p : Finset Plane) (t : Plane) :
    responsePairType (p.image (tr t)) = responsePairType p := by
  unfold responsePairType
  congr 1
  apply propext
  constructor
  · intro h x hx y hy
    rcases h (tr t x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
      (tr t y) (Finset.mem_image.mpr ⟨y, hy, rfl⟩) with h | h
    · left
      change x.1 + t.1 = y.1 + t.1 at h
      exact add_right_cancel h
    · right
      change x.2 + t.2 = y.2 + t.2 at h
      exact add_right_cancel h
  · intro h x hx y hy
    rcases Finset.mem_image.mp hx with ⟨x₀, hx₀, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨y₀, hy₀, rfl⟩
    rcases h x₀ hx₀ y₀ hy₀ with h | h
    · left
      change x₀.1 + t.1 = y₀.1 + t.1
      exact congrArg (fun z : ℤ => z + t.1) h
    · right
      change x₀.2 + t.2 = y₀.2 + t.2
      exact congrArg (fun z : ℤ => z + t.2) h

private def localLive (x : Plane) (incoming outgoing : Compass) (dead : Finset Plane) : Finset Plane :=
  ((neighbours x).erase (x - incoming.step) |>.erase (x + outgoing.step)) \ dead

private theorem neighbours_tr (x t : Plane) :
    neighbours (x + t) = (neighbours x).image (tr t) := by
  unfold neighbours tr
  rw [Finset.image_image]
  congr 1
  funext d
  simp [add_assoc, add_left_comm, add_comm]

private theorem localLive_tr (x t : Plane) (incoming outgoing : Compass) (dead : Finset Plane) :
    localLive (x + t) incoming outgoing (dead.image (tr t)) =
      (localLive x incoming outgoing dead).image (tr t) := by
  unfold localLive
  rw [neighbours_tr]
  have hin : (x + t) - incoming.step = tr t (x - incoming.step) := by
    dsimp [tr]
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hout : (x + t) + outgoing.step = tr t (x + outgoing.step) := by
    dsimp [tr]
    simp [add_assoc, add_left_comm, add_comm]
  rw [hin, hout, ← Finset.image_erase (tr_inj t), ← Finset.image_erase (tr_inj t),
    ← Finset.image_sdiff _ _ (tr_inj t)]


private def responseWeight (o : Plane) (incoming outgoing : Compass) (live p : Finset Plane) : ℚ :=
  (if o ∈ p then
    if live.card = 1 then betaPrimeBound (decide (outgoing = incoming))
    else betaBound (decide (outgoing = incoming))
  else alphaBound (decide (outgoing = incoming))) * kernelWitness (responsePairType p)

private def responseSum (o : Plane) (incoming outgoing : Compass) (live : Finset Plane) : ℚ :=
  ∑ p ∈ (insert o live).powersetCard 2, responseWeight o incoming outgoing live p

private theorem relaxedReward_eq_responseSum (x : Plane) (incoming outgoing : Compass)
    (dead : Finset Plane) :
    relaxedReward x incoming outgoing dead =
      responseSum (x + outgoing.step) incoming outgoing (localLive x incoming outgoing dead) := by
  rfl

private theorem responseSum_tr (o t : Plane) (incoming outgoing : Compass) (live : Finset Plane) :
    responseSum (o + t) incoming outgoing (live.image (tr t)) =
      responseSum o incoming outgoing live := by
  unfold responseSum
  symm
  apply Finset.sum_bij (fun p _ => p.image (tr t))
  · intro p hp
    rw [Finset.mem_powersetCard] at hp ⊢
    refine ⟨Finset.image_subset_iff.mpr ?_, ?_⟩
    · intro z hz
      rcases Finset.mem_insert.mp (hp.1 hz) with h | h
      · subst z
        simp [tr]
      · apply Finset.mem_insert.mpr
        right
        exact Finset.mem_image.mpr ⟨z, h, rfl⟩
    · rw [Finset.card_image_of_injective _ (tr_inj t), hp.2]
  · intro p hp q hq heq
    exact (Finset.image_inj (tr_inj t)).mp heq
  · intro q hq
    refine ⟨q.image (tr (-t)), ?_, ?_⟩
    · rw [Finset.mem_powersetCard] at hq ⊢
      refine ⟨Finset.image_subset_iff.mpr ?_, ?_⟩
      · intro z hz
        have hy' := hq.1 hz
        change tr (-t) z ∈ insert o live
        rw [Finset.mem_insert]
        rcases Finset.mem_insert.mp hy' with h | h
        · left
          rw [h]
          simp [tr]
        · right
          rcases Finset.mem_image.mp h with ⟨w, hw, hzw⟩
          have : z = tr t w := hzw.symm
          rw [this]
          simpa [tr, add_assoc, add_left_comm, add_comm] using hw
      · rw [Finset.card_image_of_injective _ (tr_inj (-t)), hq.2]
    · rw [Finset.image_image]
      have hfun : tr t ∘ tr (-t) = id := by
        funext z
        simp [tr]
      rw [hfun, Finset.image_id]
  · intro p hp
    have hmem : o + t ∈ (p.image (tr t)) ↔ o ∈ p := by
      rw [Finset.mem_image]
      constructor
      · rintro ⟨z, hz, h⟩
        have : z = o := by
          dsimp [tr] at h
          exact add_right_cancel h
        simpa [this] using hz
      · intro ho
        exact ⟨o, ho, rfl⟩
    unfold responseWeight
    have hcard : (live.image (tr t)).card = live.card :=
      Finset.card_image_of_injective _ (tr_inj t)
    rw [hcard, responsePairType_image_tr]
    by_cases ho : o ∈ p
    · have ho' : o + t ∈ p.image (tr t) := hmem.mpr ho
      simp [ho, ho']
    · have ho' : o + t ∉ p.image (tr t) := fun hh => ho (hmem.mp hh)
      simp [ho, ho']


private theorem betaPrime_le_beta (b : Bool) : betaPrimeBound b ≤ betaBound b := by
  cases b <;> norm_num [betaPrimeBound, betaBound]

private theorem responseWeight_nonneg (o : Plane) (incoming outgoing : Compass)
    (live p : Finset Plane) : 0 ≤ responseWeight o incoming outgoing live p := by
  unfold responseWeight
  have ha : 0 ≤ alphaBound (decide (outgoing = incoming)) := by
    cases decide (outgoing = incoming) <;> norm_num [alphaBound]
  have hb : 0 ≤ betaBound (decide (outgoing = incoming)) := by
    cases decide (outgoing = incoming) <;> norm_num [betaBound]
  have hp : 0 ≤ betaPrimeBound (decide (outgoing = incoming)) := by
    cases decide (outgoing = incoming) <;> norm_num [betaPrimeBound]
  have hw : 0 ≤ kernelWitness (responsePairType p) :=
    AKLT.Blueprint.H3.kernelWitness_pos _ |>.le
  by_cases ho : o ∈ p
  · by_cases hc : live.card = 1
    · simp [ho, hc]
      exact mul_nonneg hp hw
    · simp [ho, hc]
      exact mul_nonneg hb hw
  · simp [ho]
    exact mul_nonneg ha hw

private theorem responseSum_mono (o : Plane) (incoming outgoing : Compass)
    {liveSmall liveBig : Finset Plane} (hsub : liveSmall ⊆ liveBig) :
    responseSum o incoming outgoing liveSmall ≤ responseSum o incoming outgoing liveBig := by
  unfold responseSum
  let smallPairs := (insert o liveSmall).powersetCard 2
  let bigPairs := (insert o liveBig).powersetCard 2
  have hpairs : smallPairs ⊆ bigPairs := by
    intro p hp
    rw [Finset.mem_powersetCard] at hp ⊢
    exact ⟨Finset.Subset.trans hp.1 (Finset.insert_subset_insert o hsub), hp.2⟩
  calc
    (∑ p ∈ smallPairs, responseWeight o incoming outgoing liveSmall p) ≤
        ∑ p ∈ smallPairs, responseWeight o incoming outgoing liveBig p := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases hout : o ∈ p
      · have hp' := (Finset.mem_powersetCard.mp hp)
        have hEraseSub : p.erase o ⊆ liveSmall := by
          intro z hz
          rcases Finset.mem_erase.mp hz with ⟨hne, hzmem⟩
          rcases Finset.mem_insert.mp (hp'.1 hzmem) with h | h
          · exact False.elim (hne h)
          · exact h
        have hCardErase : (p.erase o).card = 1 := by
          rw [Finset.card_erase_of_mem hout, hp'.2]
        have hnonempty : 1 ≤ liveSmall.card := by
          have := Finset.card_le_card hEraseSub
          omega
        have hcard : liveSmall.card ≤ liveBig.card := Finset.card_le_card hsub
        have hcoeff :
            (if liveSmall.card = 1 then betaPrimeBound (decide (outgoing = incoming))
              else betaBound (decide (outgoing = incoming))) ≤
            (if liveBig.card = 1 then betaPrimeBound (decide (outgoing = incoming))
              else betaBound (decide (outgoing = incoming))) := by
          by_cases hs : liveSmall.card = 1
          · by_cases hb : liveBig.card = 1
            · simp [hs, hb]
            · simpa [hs, hb] using betaPrime_le_beta (decide (outgoing = incoming))
          · have hb : liveBig.card ≠ 1 := by
              intro h
              omega
            simp [hs, hb]
        simpa [responseWeight, hout] using
          (mul_le_mul_of_nonneg_right hcoeff
            (AKLT.Blueprint.H3.kernelWitness_pos (responsePairType p)).le)
      · simp [responseWeight, hout]
    _ ≤ ∑ p ∈ bigPairs, responseWeight o incoming outgoing liveBig p :=
      Finset.sum_le_sum_of_subset_of_nonneg hpairs (by
        intro p hp hnot
        exact responseWeight_nonneg o incoming outgoing liveBig p)

private theorem relaxedReward_mono_dead (x : Plane) (incoming outgoing : Compass)
    {deadSmall deadBig : Finset Plane} (hdead : deadSmall ⊆ deadBig) :
    relaxedReward x incoming outgoing deadBig ≤ relaxedReward x incoming outgoing deadSmall := by
  rw [relaxedReward_eq_responseSum, relaxedReward_eq_responseSum]
  apply responseSum_mono
  exact Finset.sdiff_subset_sdiff_right _ hdead

private theorem relaxedReward_tr (x t : Plane) (incoming outgoing : Compass) (dead : Finset Plane) :
    relaxedReward (x + t) incoming outgoing (dead.image (tr t)) =
      relaxedReward x incoming outgoing dead := by
  rw [relaxedReward_eq_responseSum, relaxedReward_eq_responseSum, localLive_tr]
  simpa [add_assoc, add_left_comm, add_comm] using responseSum_tr (x + outgoing.step) t incoming outgoing
    (localLive x incoming outgoing dead)


private theorem phaseDiagonal_one_fifth (φ : Phase) (k : StepKind) :
    (1 : ℚ) / 5 ≤ phaseDiagonal φ k := by
  unfold phaseDiagonal
  by_cases hk : k = .revisit
  · simp [hk]
  · cases k <;> cases φ <;> norm_num [hk, passageFactor, localThreshold]

private theorem phaseTransition_diag_one_fifth (φ : Phase) (k : StepKind) (r : ℚ) :
    (1 : ℚ) / 5 ≤ phaseTransition k r φ φ := by
  simpa [phaseTransition] using phaseDiagonal_one_fifth φ k

private theorem phaseTransition_mono_reward (k : StepKind) (φ ψ : Phase)
    {r₁ r₂ : ℚ} (hr : r₁ ≤ r₂) :
    phaseTransition k r₁ φ ψ ≤ phaseTransition k r₂ φ ψ := by
  by_cases hdiag : φ = ψ
  · simp [phaseTransition, hdiag]
  · simp only [phaseTransition, hdiag]
    by_cases hAC : φ = .A ∧ ψ = .C ∧ k = .turn
    · simp [hAC]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hr (AKLT.Blueprint.H3.passageFactor_pos false).le)
        (by norm_num)
    · by_cases hBD : φ = .B ∧ ψ = .D ∧ k = .straight
      · simp [hBD]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hr (AKLT.Blueprint.H3.passageFactor_pos true).le)
          (by norm_num)
      · simp [hAC, hBD]

/-- The stationary edge coefficient is bounded by its position-free counterpart. -/
theorem main : AKLT.Blueprint.H3.StationaryFreeEdgeStatement := by
  intro Q hQ X d₀ hd₀ φ a x d ψ
  have hfree_nonneg : 0 ≤ freeCoefficient Q φ a d ψ :=
    AKLT.Blueprint.H3.freeCoefficient_nonneg Q φ a d ψ
  by_cases hc : x = kernelCentre
  · simpa [stationaryCoefficient, hc] using hfree_nonneg
  by_cases ht : x = kernelTarget X
  · simpa [stationaryCoefficient, hc, ht] using hfree_nonneg
  by_cases hallow0 : Q.allowed a d = false
  · simp [stationaryCoefficient, freeCoefficient, hc, ht, hallow0]
  have hallow : Q.allowed a d = true := by
    cases h : Q.allowed a d <;> simp_all
  by_cases hknown : x = kernelStart ∨ x = kernelStart + d₀.step
  · by_cases hkill : ({x, x + d.step} : Finset Plane) =
        {kernelStart, kernelStart + d₀.step} ∨ Q.kind a d = .revisit
    · have hzero : stationaryCoefficient Q X d₀ φ a x d ψ = 0 := by
        simp [stationaryCoefficient, hc, ht, hallow0, hknown, hkill]
      rw [hzero]
      exact hfree_nonneg
    · by_cases hphase : φ = ψ
      · have hstat : stationaryCoefficient Q X d₀ φ a x d ψ = (1 : ℚ) / 5 := by
          simp [stationaryCoefficient, hc, ht, hallow0, hknown, hkill, hphase]
        rw [hstat]
        have hfree : freeCoefficient Q φ a d ψ =
            phaseTransition (Q.kind a d) (relaxedReward (0, 0) (Q.arrival a) d ∅) φ ψ := by
          simp [freeCoefficient, hallow]
        rw [hfree]
        simpa [hphase] using
          phaseTransition_diag_one_fifth φ (Q.kind a d)
            (relaxedReward (0, 0) (Q.arrival a) d ∅)
      · have hzero : stationaryCoefficient Q X d₀ φ a x d ψ = 0 := by
          simp [stationaryCoefficient, hc, ht, hallow0, hknown, hkill, hphase]
        rw [hzero]
        exact hfree_nonneg
  · by_cases hcentreEdge : x + d.step = kernelCentre
    · have hzero : stationaryCoefficient Q X d₀ φ a x d ψ = 0 := by
        simp [stationaryCoefficient, hc, ht, hallow0, hknown, hcentreEdge]
      rw [hzero]
      exact hfree_nonneg
    · have hshift : relaxedReward x (Q.arrival a) d {kernelCentre} =
          relaxedReward (0, 0) (Q.arrival a) d {kernelCentre - x} := by
        have htr := (relaxedReward_tr x (-x) (Q.arrival a) d
          ({kernelCentre} : Finset Plane)).symm
        have hzero : x + -x = (0, 0) := by ext <;> simp
        have hdead : ({kernelCentre} : Finset Plane).image (tr (-x)) =
            {kernelCentre - x} := by simp [tr, sub_eq_add_neg]
        rw [hzero, hdead] at htr
        have h00 : (0 : Plane) = (0, 0) := rfl
        simpa only [h00] using htr
      have hmono : relaxedReward (0, 0) (Q.arrival a) d {kernelCentre - x} ≤
          relaxedReward (0, 0) (Q.arrival a) d ∅ := by
        apply relaxedReward_mono_dead (0, 0) (Q.arrival a) d
        intro z hz
        simp at hz
      have hreward : relaxedReward x (Q.arrival a) d {kernelCentre} ≤
          relaxedReward (0, 0) (Q.arrival a) d ∅ := hshift.le.trans hmono
      have hstat : stationaryCoefficient Q X d₀ φ a x d ψ =
          phaseTransition (Q.kind a d) (relaxedReward x (Q.arrival a) d {kernelCentre}) φ ψ := by
        simp [stationaryCoefficient, hc, ht, hallow0, hknown, hcentreEdge]
      have hfree : freeCoefficient Q φ a d ψ =
          phaseTransition (Q.kind a d) (relaxedReward (0, 0) (Q.arrival a) d ∅) φ ψ := by
        simp [freeCoefficient, hallow]
      rw [hstat, hfree]
      exact phaseTransition_mono_reward (Q.kind a d) φ ψ hreward

end AKLT.W.H3M020
