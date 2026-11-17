module
public import AKLT.W.Q050.Edges

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Challenge AKLT.Blueprint.Q

namespace AKLT.W.Q050
attribute [local instance] Classical.propDecidable

private theorem frameBound_pos : 0 < frameBound := by
  have hs : Real.sqrt (5 : ℝ) * Real.sqrt 5 = 5 := by
    rw [← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
  dsimp [frameBound]
  nlinarith [Real.sqrt_nonneg (5 : ℝ)]

private theorem interaction_pos (hBounds : interactionBounds)
    (κ : Plane → Fin 3) (hκ : ProperPlaneColoring κ)
    (a b : Plane) (ha : Adjacent a b) (u v : IcoLetter) :
    0 < 1 + dot (frameVector (κ a) u) (frameVector (κ b) v) := by
  have hcol : κ a ≠ κ b := hκ a b ha
  exact lt_of_lt_of_le frameBound_pos (hBounds (κ a) (κ b) hcol u v).1

private theorem adjacent_of_internal {W : Finset Plane} {e : Plane × Plane}
    (he : e ∈ internalBonds W) : Adjacent e.1 e.2 := by
  classical
  simp only [internalBonds, Finset.mem_biUnion, Finset.mem_image, Finset.mem_inter] at he
  rcases he with ⟨x, hx, y, hy, heq⟩
  cases heq
  simp only [positiveNeighbors, Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy.1 with hy | hy
  · change Adjacent x y
    rw [hy]
    norm_num [Adjacent, latticeDist]
  · change Adjacent x y
    rw [hy]
    norm_num [Adjacent, latticeDist]

private theorem adjacent_of_leg {W : Finset Plane} {e : Plane × Plane}
    (he : e ∈ originalLegs W) : Adjacent e.1 e.2 := by
  classical
  simp only [originalLegs, Finset.mem_biUnion, Finset.mem_image, Finset.mem_sdiff] at he
  rcases he with ⟨x, hx, y, hy, heq⟩
  cases heq
  change y ∈ neighbors x ∧ y ∉ W at hy
  simp only [neighbors, Finset.mem_image, Finset.mem_univ, true_and] at hy
  rcases hy.1 with ⟨d, hd⟩
  change Adjacent x y
  rw [← hd]
  cases d <;> norm_num [Adjacent, latticeDist, Compass.step]

private theorem planeWeight_pos (hBounds : interactionBounds)
    (κ : Plane → Fin 3) (hκ : ProperPlaneColoring κ)
    (W : Finset Plane) (η : FrameBoundary W) (σ : PlaneConfiguration W) :
    0 < planeWeight κ W η σ := by
  unfold planeWeight
  apply mul_pos
  · apply mul_pos
    · positivity
    · apply Finset.prod_pos
      intro e he
      exact interaction_pos hBounds κ hκ e.1 e.2 (adjacent_of_internal he)
        (extendLetters σ e.1) (extendLetters σ e.2)
  · apply Finset.prod_pos
    intro e he
    exact interaction_pos hBounds κ hκ e.1 e.2 (adjacent_of_leg he)
      (extendLetters σ e.1) (extendBoundary η e.2)

private def restrictConfig {W V : Finset Plane} (hVW : V ⊆ W)
    (τ : PlaneConfiguration W) : PlaneConfiguration V :=
  fun x => τ ⟨x, hVW x.property⟩

private def fixedExterior {W : Finset Plane} (V : Finset Plane)
    (σ τ : PlaneConfiguration W) : Prop :=
  ∀ x, x ∈ W \ V → extendLetters τ x = extendLetters σ x

private theorem fixedExterior_glue {W V : Finset Plane} (_hVW : V ⊆ W)
    (σ : PlaneConfiguration W) (v : PlaneConfiguration V) :
    fixedExterior V σ (glueConfig _hVW σ v) := by
  intro x hx
  have hxW : x ∈ W := (Finset.mem_sdiff.mp hx).1
  have hxV : x ∉ V := (Finset.mem_sdiff.mp hx).2
  simp [glueConfig, extendLetters, hxW, hxV]

private theorem restrict_glue {W V : Finset Plane} (hVW : V ⊆ W)
    (σ : PlaneConfiguration W) (v : PlaneConfiguration V) :
    restrictConfig hVW (glueConfig hVW σ v) = v := by
  funext x
  simp [restrictConfig, glueConfig, x.property]

private theorem glue_restrict {W V : Finset Plane} (hVW : V ⊆ W)
    (σ τ : PlaneConfiguration W) (hE : fixedExterior V σ τ) :
    glueConfig hVW σ (restrictConfig hVW τ) = τ := by
  funext x
  by_cases hx : (x : Plane) ∈ V
  · simp [glueConfig, restrictConfig, hx]
  · have hdiff : x.val ∈ W \ V := Finset.mem_sdiff.mpr ⟨x.property, hx⟩
    have hfix := hE x.val hdiff
    have hfix' : τ x = σ x := by
      simpa [extendLetters, x.property] using hfix
    simpa [glueConfig, hx] using hfix'.symm

private theorem sum_fixedExterior {W V : Finset Plane} (hVW : V ⊆ W)
    (σ : PlaneConfiguration W) (f : PlaneConfiguration W → ℝ) :
    (∑ τ, if fixedExterior V σ τ then f τ else 0) =
      ∑ v, f (glueConfig hVW σ v) := by
  classical
  rw [← Finset.sum_filter]
  refine Finset.sum_bij'
    (fun τ _ => restrictConfig hVW τ)
    (fun v _ => glueConfig hVW σ v) ?_ ?_ ?_ ?_ ?_
  · intro τ hτ
    exact Finset.mem_univ _
  · intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fixedExterior_glue hVW σ v⟩
  · intro τ hτ
    exact glue_restrict hVW σ τ (Finset.mem_filter.mp hτ).2
  · intro v hv
    exact restrict_glue hVW σ v
  · intro τ hτ
    exact congrArg f (glue_restrict hVW σ τ (Finset.mem_filter.mp hτ).2).symm

private theorem marginal_conditionOn_fiber {Ω Ξ : Type} [Fintype Ω] [DecidableEq Ξ]
    (p : Ω → ℝ) (s : Ω → Prop) (r : Ω → Ξ) (g : Ξ → Ω)
    (hg : ∀ z, s (g z)) (hrg : ∀ z, r (g z) = z)
    (huniq : ∀ x, s x → g (r x) = x) (z : Ξ) :
    marginal (conditionOn p s) r z = p (g z) / (∑ x, if s x then p x else 0) := by
  classical
  let D : ℝ := ∑ x, if s x then p x else 0
  have hcond : ∀ x, conditionOn p s x = if s x then p x / D else 0 := by
    intro x
    by_cases hs : s x
    · simp [conditionOn, AKLT.Defs.normalize, D, hs]
    · simp [conditionOn, AKLT.Defs.normalize, hs]
  unfold marginal
  simp_rw [hcond]
  rw [Finset.sum_eq_single (g z)]
  · simp [hg z, hrg z, D]
  · intro x hx hne
    by_cases hs : s x
    · by_cases hr : r x = z
      · have hxg : g z = x := by simpa [hr] using huniq x hs
        exact (hne hxg.symm).elim
      · simp [hr]
    · simp [hs]
  · intro hnot
    exact (hnot (Finset.mem_univ _)).elim

private theorem conditionalPlaneLaw_eq_fiberNormalize
    (hBounds : interactionBounds) (κ : Plane → Fin 3) (hκ : ProperPlaneColoring κ)
    (W V : Finset Plane) (η : FrameBoundary W) (hVW : V ⊆ W)
    (σ : PlaneConfiguration W) :
    conditionalPlaneLaw κ W V η σ =
      AKLT.Defs.normalize (fun v : PlaneConfiguration V =>
        planeWeight κ W η (glueConfig hVW σ v)) := by
  classical
  let w : PlaneConfiguration W → ℝ := planeWeight κ W η
  let E : PlaneConfiguration W → Prop := fixedExterior V σ
  let Z : ℝ := ∑ τ, w τ
  let ZE : ℝ := ∑ τ, if E τ then w τ else 0
  have hZ : 0 < Z := by
    apply Finset.sum_pos
    · intro τ hτ
      exact planeWeight_pos hBounds κ hκ W η τ
    · exact Finset.univ_nonempty
  have hFiber : ZE = ∑ v : PlaneConfiguration V, w (glueConfig hVW σ v) := by
    simpa [E, ZE, w] using sum_fixedExterior hVW σ w
  have hZE : 0 < ZE := by
    rw [hFiber]
    apply Finset.sum_pos
    · intro v hv
      exact planeWeight_pos hBounds κ hκ W η (glueConfig hVW σ v)
    · exact Finset.univ_nonempty
  have hDen :
      (∑ τ, if E τ then AKLT.Defs.normalize w τ else 0) = ZE / Z := by
    calc
      (∑ τ, if E τ then AKLT.Defs.normalize w τ else 0) =
          ∑ τ, (if E τ then w τ else 0) / Z := by
        apply Finset.sum_congr rfl
        intro τ hτ
        by_cases hE : E τ <;> simp [AKLT.Defs.normalize, Z, hE]
      _ = ZE / Z := by
        rw [← Finset.sum_div]
  have hmap : (fun τ : PlaneConfiguration W => fun x : V => extendLetters τ x.val) =
      restrictConfig hVW := by
    funext τ x
    simp [restrictConfig, extendLetters, hVW x.property]
  funext v
  change marginal (conditionOn (planeLaw κ W η) E)
      (fun τ : PlaneConfiguration W => fun x : V => extendLetters τ x.val) v = _
  rw [hmap]
  change marginal (conditionOn (AKLT.Defs.normalize w) E) (restrictConfig hVW) v = _
  rw [marginal_conditionOn_fiber (AKLT.Defs.normalize w) E
    (restrictConfig hVW) (glueConfig hVW σ)
    (fixedExterior_glue hVW σ) (restrict_glue hVW σ)
    (fun τ hτ => glue_restrict hVW σ τ hτ) v]
  rw [hDen, hFiber]
  simp only [AKLT.Defs.normalize]
  dsimp [w]
  dsimp [Z, w] at hZ
  dsimp [ZE, w] at hZE
  dsimp [Z, w]
  field_simp [ne_of_gt hZ, ne_of_gt hZE]

/-- Conditioning on the exterior letters gives the smaller-volume plane law
with its induced boundary, including empty volumes. -/
theorem main : AKLT.Blueprint.Q.PlaneConditioningStatement := by
  classical
  intro hBounds κ hκ W η V hVW σ
  obtain ⟨c, hcfact⟩ := fiberWeightFactorization κ W η V hVW σ
  let v₀ := restrictConfig hVW σ
  have hc : 0 < c := by
    have hp := planeWeight_pos hBounds κ hκ W η (glueConfig hVW σ v₀)
    rw [hcfact v₀] at hp
    exact (mul_pos_iff_of_pos_right
      (planeWeight_pos hBounds κ hκ V (inducedBoundary W V η σ) v₀)).mp hp
  have hFiber := conditionalPlaneLaw_eq_fiberNormalize hBounds κ hκ W V η hVW σ
  let q : PlaneConfiguration V → ℝ := planeWeight κ V (inducedBoundary W V η σ)
  have hVsum : 0 < ∑ v : PlaneConfiguration V, q v := by
    apply Finset.sum_pos
    · intro v hv
      exact planeWeight_pos hBounds κ hκ V (inducedBoundary W V η σ) v
    · exact Finset.univ_nonempty
  have hsum :
      (∑ v : PlaneConfiguration V, planeWeight κ W η (glueConfig hVW σ v)) =
        c * ∑ v : PlaneConfiguration V, q v := by
    calc
      (∑ v, planeWeight κ W η (glueConfig hVW σ v)) =
          ∑ v, c * q v := by
        apply Finset.sum_congr rfl
        intro v hv
        exact hcfact v
      _ = c * ∑ v, q v := by rw [← Finset.mul_sum]
  have hnorm :
      AKLT.Defs.normalize (fun v : PlaneConfiguration V =>
        planeWeight κ W η (glueConfig hVW σ v)) = AKLT.Defs.normalize q := by
    funext v
    simp only [AKLT.Defs.normalize]
    rw [hcfact v, hsum]
    field_simp [ne_of_gt hc, ne_of_gt hVsum]
    ring
  calc
    conditionalPlaneLaw κ W V η σ =
        AKLT.Defs.normalize (fun v : PlaneConfiguration V =>
          planeWeight κ W η (glueConfig hVW σ v)) := hFiber
    _ = AKLT.Defs.normalize q := hnorm
    _ = planeLaw κ V (inducedBoundary W V η σ) := rfl.symm

end AKLT.W.Q050
