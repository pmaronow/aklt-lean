import AKLT.Blueprint.Gap.NodesPeriodic

noncomputable section
set_option maxHeartbeats 800000
open AKLT.Defs AKLT.Challenge AKLT.Blueprint.Gap

namespace AKLT.W.GAP041

attribute [local instance] Classical.propDecidable

/-- The supplied plane-site assignment estimate, reindexed to the actual
finite product coordinates of `W`. -/
theorem main : AKLT.Blueprint.Gap.FrameSpecEnergyStatement := by
  classical
  intro κ hPlane
  unfold SpecEnergy
  intro W η
  let boundary : FrameBoundary W := fun z => η z
  change AssignmentBound (planeLaw κ W boundary) frameEnergy
  change ∀ U J : Finset W, Disjoint U J →
    ∀ a b : (x : W) → IcoLetter,
      frameEnergy ^ U.card ≤ conditionalProbability (planeLaw κ W boundary)
        (fun σ => ∀ x ∈ J, σ x = a x)
        (fun σ => ∀ x ∈ U, σ x = b x)
  intro U J hDisj a b
  let Uplane : Finset Plane := U.image Subtype.val
  let Jplane : Finset Plane := J.image Subtype.val
  let totalA : Plane → IcoLetter := fun x =>
    if hx : x ∈ W then a ⟨x, hx⟩ else (0, 0, 0)
  let totalB : Plane → IcoLetter := fun x =>
    if hx : x ∈ W then b ⟨x, hx⟩ else (0, 0, 0)
  have hUsub : Uplane ⊆ W := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨u, hu, rfl⟩
    exact u.property
  have hJsub : Jplane ⊆ W := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
    exact j.property
  have hUdisj : Disjoint Uplane Jplane := by
    apply Finset.disjoint_left.mpr
    intro x hxU hxJ
    rcases Finset.mem_image.mp hxU with ⟨u, hu, rfl⟩
    rcases Finset.mem_image.mp hxJ with ⟨j, hj, huv⟩
    have heq : u = j := Subtype.ext huv.symm
    have hnot : u ∉ J := Finset.disjoint_left.mp hDisj hu
    exact hnot (by simpa [heq] using hj)
  have hUcard : Uplane.card = U.card := by
    dsimp [Uplane]
    rw [Finset.card_image_of_injective _ Subtype.val_injective]
  have hJevent :
      (fun σ : (x : W) → IcoLetter => ∀ x ∈ J, σ x = a x) =
      (fun σ => ∀ x ∈ Jplane, extendLetters σ x = totalA x) := by
    funext σ
    apply propext
    constructor
    · intro h x hx
      rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
      simpa [extendLetters, totalA, j.property] using h j hj
    · intro h j hj
      have hx : (j : Plane) ∈ Jplane := Finset.mem_image.mpr ⟨j, hj, rfl⟩
      simpa [extendLetters, totalA, j.property] using h j.val hx
  have hUevent :
      (fun σ : (x : W) → IcoLetter => ∀ x ∈ U, σ x = b x) =
      (fun σ => ∀ x ∈ Uplane, extendLetters σ x = totalB x) := by
    funext σ
    apply propext
    constructor
    · intro h x hx
      rcases Finset.mem_image.mp hx with ⟨u, hu, rfl⟩
      simpa [extendLetters, totalB, u.property] using h u hu
    · intro h u hu
      have hx : (u : Plane) ∈ Uplane := Finset.mem_image.mpr ⟨u, hu, rfl⟩
      simpa [extendLetters, totalB, u.property] using h u.val hx
  have hbound := hPlane W boundary Uplane Jplane hUsub hJsub hUdisj totalA totalB
  rw [← hJevent, ← hUevent] at hbound
  rw [hUcard] at hbound
  exact hbound

end AKLT.W.GAP041
