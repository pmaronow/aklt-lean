module
public import CertData.H3.Bridge.Interface

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

set_option maxHeartbeats 1000000

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.H3C026

-- Translation of the finite local response sum.
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
  ((neighbors x).erase (x - incoming.step) |>.erase (x + outgoing.step)) \ dead

private theorem neighbors_tr (x t : Plane) :
    neighbors (x + t) = (neighbors x).image (tr t) := by
  unfold neighbors tr
  rw [Finset.image_image]
  congr 1
  funext d
  simp [add_assoc, add_left_comm, add_comm]

private theorem localLive_tr (x t : Plane) (incoming outgoing : Compass) (dead : Finset Plane) :
    localLive (x + t) incoming outgoing (dead.image (tr t)) =
      (localLive x incoming outgoing dead).image (tr t) := by
  unfold localLive
  rw [neighbors_tr]
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

theorem relaxedReward_tr (x t : Plane) (incoming outgoing : Compass) (dead : Finset Plane) :
    relaxedReward (x + t) incoming outgoing (dead.image (tr t)) =
      relaxedReward x incoming outgoing dead := by
  rw [relaxedReward_eq_responseSum, relaxedReward_eq_responseSum, localLive_tr]
  simpa [add_assoc, add_left_comm, add_comm] using responseSum_tr (x + outgoing.step) t incoming outgoing
    (localLive x incoming outgoing dead)


theorem relaxedReward_far (x : Plane) (incoming outgoing : Compass)
    (hx : ∀ d : Compass, x ≠ -d.step) :
    relaxedReward x incoming outgoing {kernelCenter} =
      relaxedReward (0,0) incoming outgoing ∅ := by
  have hnot : kernelCenter ∉ neighbors x := by
    rintro h
    rcases Finset.mem_image.mp h with ⟨d, hd, he⟩
    apply hx d
    change x + d.step = 0 at he
    exact eq_neg_of_add_eq_zero_left he
  have hnot' : kernelCenter ∉
      ((neighbors x).erase (x - incoming.step)).erase (x + outgoing.step) := by
    intro h
    exact hnot (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
  have heq : relaxedReward x incoming outgoing {kernelCenter} =
      relaxedReward x incoming outgoing ∅ := by
    simp only [relaxedReward, Finset.sdiff_singleton_eq_erase,
      Finset.erase_eq_of_notMem hnot', Finset.sdiff_empty]
  rw [heq]
  simpa only [show ((0,0) : Plane) = 0 from rfl, zero_add, Finset.image_empty]
    using relaxedReward_tr (0,0) x incoming outgoing ∅

end AKLT.W.H3C026

#print axioms AKLT.W.H3C026.relaxedReward_tr
#print axioms AKLT.W.H3C026.relaxedReward_far
