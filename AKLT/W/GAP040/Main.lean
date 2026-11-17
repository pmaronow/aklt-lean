import AKLT.Blueprint.Gap.NodesPeriodic

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Challenge AKLT.Blueprint.Gap
attribute [local instance] Classical.propDecidable

namespace AKLT.W.GAP040

local instance (α : Type) : DecidableEq α := Classical.decEq α

private theorem planeWeight_eq_of_boundary_eq
    (κ : Plane → Fin 3) (W : Finset Plane)
    (η ξ : FrameBoundary W)
    (hηξ : ∀ z : exteriorSites W, η z = ξ z) :
    ∀ σ : PlaneConfiguration W, planeWeight κ W η σ = planeWeight κ W ξ σ := by
  intro σ
  have hfactor : ∀ e ∈ originalLegs W,
      extendBoundary η e.2 = extendBoundary ξ e.2 := by
    intro e he
    have hext : e.2 ∈ exteriorSites W := Finset.mem_image.mpr ⟨e, he, rfl⟩
    simp only [extendBoundary, dite_eq_left hext]
    exact hηξ ⟨e.2, hext⟩
  have hprod :
      (∏ e ∈ originalLegs W, (1 + dot (frameVector (κ e.1) (extendLetters σ e.1))
        (frameVector (κ e.2) (extendBoundary η e.2)))) =
      (∏ e ∈ originalLegs W, (1 + dot (frameVector (κ e.1) (extendLetters σ e.1))
        (frameVector (κ e.2) (extendBoundary ξ e.2)))) := by
    apply Finset.prod_congr rfl
    intro e he
    simp only [hfactor e he]
  unfold planeWeight
  rw [hprod]

private theorem planeLaw_eq_of_boundary_eq
    (κ : Plane → Fin 3) (W : Finset Plane)
    (η ξ : FrameBoundary W)
    (hηξ : ∀ z : exteriorSites W, η z = ξ z) :
    planeLaw κ W η = planeLaw κ W ξ := by
  have hw : planeWeight κ W η = planeWeight κ W ξ := by
    funext σ
    exact planeWeight_eq_of_boundary_eq κ W η ξ hηξ σ
  funext σ
  change AKLT.Defs.normalize (planeWeight κ W η) σ =
    AKLT.Defs.normalize (planeWeight κ W ξ) σ
  rw [hw]

private theorem marginal_decEq_irrel {Ω Ξ : Type*} [Fintype Ω]
    (p : Weight Ω) (r : Ω → Ξ) (d₁ d₂ : DecidableEq Ξ) :
    @marginal Ω Ξ ‹Fintype Ω› d₁ p r = @marginal Ω Ξ ‹Fintype Ω› d₂ p r := by
  funext z
  unfold marginal
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : r x = z <;> simp [h]

private theorem neighbour_supDist_eq_one {x y : Plane}
    (h : y ∈ neighbours x) : supDist y x = 1 := by
  rcases Finset.mem_image.mp h with ⟨d, _, rfl⟩
  cases d <;> simp [supDist, Compass.step]

private theorem neighbour_mem_exteriorSites
    {W : Finset Plane} {x y : Plane}
    (hx : x ∈ W) (hy : y ∈ neighbours x \ W) :
    y ∈ exteriorSites W := by
  change y ∈ (originalLegs W).image Prod.snd
  refine Finset.mem_image.mpr ⟨(x, y), ?_, rfl⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨x, hx, ?_⟩
  exact Finset.mem_image.mpr ⟨y, hy, rfl⟩

private theorem exteriorSites_subset_of_outside
    {V W : Finset Plane} (hVW : V ⊆ W) {z : Plane}
    (hzV : z ∈ exteriorSites V) (hzW : z ∉ W) : z ∈ exteriorSites W := by
  change z ∈ (originalLegs V).image Prod.snd at hzV
  obtain ⟨e, he, hez⟩ := Finset.mem_image.mp hzV
  rcases Finset.mem_biUnion.mp he with ⟨x, hxV, hxe⟩
  obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hxe
  have heq : e = (x, y) := hxy.symm
  have hyz : y = z := by simpa [heq] using hez
  have hyW : y ∉ W := by
    intro hyin
    apply hzW
    simpa [hyz] using hyin
  change z ∈ (originalLegs W).image Prod.snd
  refine Finset.mem_image.mpr ⟨(x, y), ?_, hyz⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨x, hVW hxV, ?_⟩
  exact Finset.mem_image.mpr ⟨y,
    Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hy).1, hyW⟩, rfl⟩

theorem main : AKLT.Blueprint.Gap.FrameSpecRegularityStatement := by
  intro κ hκ hpositive hconsistency
  refine ⟨?_, ?_, ?_⟩
  · intro W η
    change PositiveProbability (planeLaw κ W (fun z : exteriorSites W => η z.val))
    exact hpositive W (fun z => η z.val)
  · intro W V hVW η σ
    dsimp [frameSpec, PlaneConfig] at η σ ⊢
    let ηB : FrameBoundary W := fun z => η z.val
    have hfinite := hconsistency W V hVW ηB σ
    have hevent :
        (fun τ : PlaneConfiguration W => ∀ x : W, x.val ∉ V → τ x = σ x) =
        (fun τ => ∀ x ∈ W \ V, extendLetters τ x = extendLetters σ x) := by
      funext τ
      apply propext
      constructor
      · intro h x hx
        have hx' := Finset.mem_sdiff.mp hx
        have hh := h ⟨x, hx'.1⟩ hx'.2
        have hτ : extendLetters τ x = τ ⟨x, hx'.1⟩ := by
          simp [extendLetters, hx'.1]
        have hσ : extendLetters σ x = σ ⟨x, hx'.1⟩ := by
          simp [extendLetters, hx'.1]
        rw [hτ, hσ, hh]
      · intro h x hxV
        have hx' : x.val ∈ W \ V := Finset.mem_sdiff.mpr ⟨x.property, hxV⟩
        have hh := h x.val hx'
        have hτ : extendLetters τ x.val = τ x := by simp [extendLetters]
        have hσ : extendLetters σ x.val = σ x := by simp [extendLetters]
        rw [hτ, hσ] at hh
        exact hh
    have hmap :
        (fun τ : PlaneConfiguration W => fun x : V =>
          restrict V (fill (frameSpec κ) W η τ) x) =
        (fun τ x => extendLetters τ x.val) := by
      funext τ
      funext x
      simp [restrict, fill, frameSpec, extendLetters, hVW x.property]
    have hboundary :
        (fun z : exteriorSites V => fill (frameSpec κ) W η σ z.val) =
        inducedBoundary W V ηB σ := by
      funext z
      by_cases hzW : z.val ∈ W
      · simp [inducedBoundary, fill, frameSpec, hzW, extendLetters]
      · have hzExt := exteriorSites_subset_of_outside hVW z.property hzW
        simp [inducedBoundary, fill, frameSpec, hzW, extendBoundary, ηB, hzExt]
    have hleft :
        marginal (conditionOn (planeLaw κ W (fun z => η z))
          (fun τ : PlaneConfiguration W => ∀ x : W, x.val ∉ V → τ x = σ x))
          (fun τ : PlaneConfiguration W => fun x : V =>
            restrict V (fill (frameSpec κ) W η τ) x) = conditionalPlaneLaw κ W V ηB σ := by
      unfold conditionalPlaneLaw
      rw [hevent, hmap]
      have hηB : (fun z : exteriorSites W => η z) = ηB := rfl
      rw [hηB]
      exact marginal_decEq_irrel _ _ _ _
    have hright : planeLaw κ V (inducedBoundary W V ηB σ) =
        planeLaw κ V (fun z => fill (frameSpec κ) W η σ z) := by
      simpa [frameSpec, PlaneConfig] using congrArg (planeLaw κ V) hboundary.symm
    have hmid : conditionalPlaneLaw κ W V ηB σ =
        planeLaw κ V (inducedBoundary W V ηB σ) := by
      simpa [frameSpec, PlaneConfig] using hfinite
    exact hleft.trans (hmid.trans hright)
  · intro W η ξ hagree
    dsimp [frameSpec] at η ξ ⊢
    change planeLaw κ W (fun z : exteriorSites W => η z.val) =
      planeLaw κ W (fun z : exteriorSites W => ξ z.val)
    apply planeLaw_eq_of_boundary_eq κ W
    intro z
    have hz : z.val ∈ exteriorSites W := z.property
    have he : ∃ e ∈ originalLegs W, e.2 = z.val := by
      change z.val ∈ (originalLegs W).image Prod.snd at hz
      exact Finset.mem_image.mp hz
    obtain ⟨e, hemem, hez⟩ := he
    rcases Finset.mem_biUnion.mp hemem with ⟨x, hxW, hrest⟩
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hrest
    have hyW : y ∉ W := (Finset.mem_sdiff.mp hy).2
    have hdist : setDistance supDist y (↑W : Set Plane) ≤ 1 := by
      have hle : setDistance supDist y (↑W : Set Plane) ≤ (supDist y x : ℕ∞) := by
        have hxSet : x ∈ (↑W : Set Plane) := by simpa using hxW
        unfold setDistance
        exact iInf_le
          (fun q : {q : Plane // q ∈ (↑W : Set Plane)} => (supDist y q.val : ℕ∞))
          ⟨x, hxSet⟩
      rw [neighbour_supDist_eq_one ((Finset.mem_sdiff.mp hy).1)] at hle
      exact hle
    have hagree' := hagree y hyW hdist
    have heq : e = (x, y) := hxy.symm
    have hyz : y = z.val := by simpa [heq] using hez
    rw [← hyz]
    exact hagree'

end AKLT.W.GAP040

end
