module
public import AKLT.Blueprint.Win.NodesCut

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.WIN067

private theorem originalLeg_facts {G : Finset Plane} (e : originalLegs G) :
    Adjacent e.val.1 e.val.2 ∧ e.val.2 ∉ G := by
  classical
  have he : e.val ∈ originalLegs G := e.property
  unfold originalLegs at he
  rcases Finset.mem_biUnion.mp he with ⟨x, hx, hmem⟩
  rcases Finset.mem_image.mp hmem with ⟨z, hz, hpair⟩
  have hcoords : e.val.1 = x ∧ e.val.2 = z := by
    constructor
    · have hh := congrArg Prod.fst hpair.symm
      simpa using hh
    · have hh := congrArg Prod.snd hpair.symm
      simpa using hh
  have hz' : z ∈ neighbours x ∧ z ∉ G := Finset.mem_sdiff.mp hz
  have hnot : e.val.2 ∉ G := by rw [hcoords.2]; exact hz'.2
  unfold neighbours at hz'
  rcases Finset.mem_image.mp hz'.1 with ⟨d, _, hdz⟩
  have hadj : Adjacent x z := by
    rw [← hdz]
    cases d <;> simp [Adjacent, latticeDist, Compass.step]
  constructor
  · simpa [hcoords.1, hcoords.2] using hadj
  · exact hnot

private theorem pinnedSum_eq_on_retained_tails
    (G Y : Finset Plane) (τ τ' : PinAssignment G)
    (f : (Plane → Vec3) → ℝ)
    (hτ : ∀ e : originalLegs G, e.val.1 ∈ G \ Y → τ e = τ' e) :
    pinnedSum G Y τ f = pinnedSum G Y τ' f := by
  classical
  unfold pinnedSum
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  apply Finset.prod_congr rfl
  intro e he
  by_cases hactive : e.val.1 ∈ G \ Y
  · simp [hτ e hactive]
  · simp [hactive]

private theorem active_tail_mem {G H : Finset Plane}
    {x : Plane} (hx : x ∈ G \ (G \ H)) : x ∈ H := by
  rcases Finset.mem_sdiff.mp hx with ⟨hxG, hxnot⟩
  by_contra hxH
  exact hxnot (Finset.mem_sdiff.mpr ⟨hxG, hxH⟩)

theorem main : AKLT.Blueprint.Win.ComponentPinsStatement := by
  classical
  intro κ F B X G₁ G₂ hcut unit η ξ s t
  rcases hcut with ⟨hBF, hBext, hX, hdisj, hpieces, hno12, hno1ext, hno2B⟩
  have hG1sub : G₁ ⊆ F \ B := by
    intro x hx
    have hxunion : x ∈ G₁ ∪ G₂ := Finset.mem_union.mpr (Or.inl hx)
    rw [hpieces] at hxunion
    exact (Finset.mem_sdiff.mp hxunion).1
  have hG2sub : G₂ ⊆ F \ B := by
    intro x hx
    have hxunion : x ∈ G₁ ∪ G₂ := Finset.mem_union.mpr (Or.inr hx)
    rw [hpieces] at hxunion
    exact (Finset.mem_sdiff.mp hxunion).1
  constructor
  · apply pinnedSum_eq_on_retained_tails
    intro e hactive
    have htail : e.val.1 ∈ G₁ := active_tail_mem hactive
    have ⟨hadj, hext⟩ := originalLeg_facts e
    have hendF : e.val.2 ∈ F := by
      by_contra hnotF
      exact hno1ext e.val.1 (by simpa using htail) e.val.2 (by simpa using hnotF) hadj
    have hendB : e.val.2 ∈ B := by
      by_contra hnotB
      exact hext (Finset.mem_sdiff.mpr ⟨hendF, hnotB⟩)
    apply Subtype.ext
    simp [AKLT.Blueprint.Win.cutPins, hendB]
  · apply pinnedSum_eq_on_retained_tails
    intro e hactive
    have htail : e.val.1 ∈ G₂ := active_tail_mem hactive
    have ⟨hadj, _hext⟩ := originalLeg_facts e
    have hendB : e.val.2 ∉ B := by
      intro hendB
      exact hno2B e.val.1 (by simpa using htail) e.val.2 (by simpa using hendB) hadj
    apply Subtype.ext
    simp [AKLT.Blueprint.Win.cutPins, hendB]

end AKLT.W.WIN067
