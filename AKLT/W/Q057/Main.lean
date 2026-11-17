import AKLT.Blueprint.Q.NodesEnergy

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Q

namespace AKLT.W.Q057

private lemma frameBound_pos : 0 < frameBound := by
  unfold frameBound
  have hs : Real.sqrt (5 : ℝ) < 5 := by
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
    have hnonneg := Real.sqrt_nonneg (5 : ℝ)
    nlinarith
  positivity

private lemma originalLeg_source_mem {W : Finset Plane} {e : Plane × Plane}
    (he : e ∈ originalLegs W) : e.1 ∈ W := by
  simp only [originalLegs, Finset.mem_biUnion, Finset.mem_image] at he
  rcases he with ⟨x, hx, z, hz, h⟩
  cases h
  exact hx

private lemma originalLeg_adjacent {W : Finset Plane} {e : Plane × Plane}
    (he : e ∈ originalLegs W) : Adjacent e.1 e.2 := by
  simp only [originalLegs, Finset.mem_biUnion, Finset.mem_image] at he
  rcases he with ⟨x, hx, z, hz, rfl⟩
  rcases Finset.mem_sdiff.mp hz with ⟨hzmem, hznmem⟩
  change z ∈ Finset.univ.image (fun d : Compass => x + d.step) at hzmem
  rcases Finset.mem_image.mp hzmem with ⟨d, hd, hEq⟩
  change Adjacent x z
  rw [← hEq]
  cases d <;> simp [Adjacent, latticeDist, Compass.step]

private lemma internalBond_adjacent {W : Finset Plane} {e : Plane × Plane}
    (he : e ∈ internalBonds W) : Adjacent e.1 e.2 := by
  simp only [internalBonds, Finset.mem_biUnion, Finset.mem_image] at he
  rcases he with ⟨x, hx, y, hy, rfl⟩
  rcases Finset.mem_inter.mp hy with ⟨hypos, hyW⟩
  simp only [positiveNeighbours, Finset.mem_insert, Finset.mem_singleton] at hypos
  rcases hypos with hy | hy
  · rw [hy]
    simp [Adjacent, latticeDist]
  · rw [hy]
    simp [Adjacent, latticeDist]

private lemma frameInteraction_pos (κ : Plane → Fin 3) (hBounds : interactionBounds)
    (hκ : ProperPlaneColouring κ) {x y : Plane} (hadj : Adjacent x y)
    (a b : IcoLetter) : 0 < 1 + dot (frameVector (κ x) a) (frameVector (κ y) b) := by
  have hcol := hκ x y hadj
  exact lt_of_lt_of_le frameBound_pos (hBounds (κ x) (κ y) hcol a b).1

private def siteNormalizer {W : Finset Plane} (κ : Plane → Fin 3)
    (η : FrameBoundary W) (x : W) : ℝ :=
  ∑ a : IcoLetter, planeSiteWeight κ W η x a

set_option maxHeartbeats 400000 in
private lemma planeSiteWeight_pos {W : Finset Plane} (κ : Plane → Fin 3)
    (hBounds : interactionBounds) (hκ : ProperPlaneColouring κ)
    (η : FrameBoundary W) (x : W) (a : IcoLetter) :
    0 < planeSiteWeight κ W η x a := by
  unfold planeSiteWeight
  apply mul_pos (by norm_num)
  apply Finset.prod_pos
  intro e he
  have hmem := (Finset.mem_filter.mp he).1
  have hpos := frameInteraction_pos κ hBounds hκ (originalLeg_adjacent hmem)
    a (extendBoundary η e.2)
  rw [(Finset.mem_filter.mp he).2] at hpos
  exact hpos

private lemma siteNormalizer_pos {W : Finset Plane} (κ : Plane → Fin 3)
    (hBounds : interactionBounds) (hκ : ProperPlaneColouring κ)
    (η : FrameBoundary W) (x : W) : 0 < siteNormalizer κ η x := by
  unfold siteNormalizer
  apply Finset.sum_pos
  · intro a ha
    exact planeSiteWeight_pos κ hBounds hκ η x a
  · exact Finset.univ_nonempty

private lemma planeInteraction_pos {W : Finset Plane} (κ : Plane → Fin 3)
    (hBounds : interactionBounds) (hκ : ProperPlaneColouring κ)
    (σ : PlaneConfiguration W) : 0 < planeInteraction κ W σ := by
  unfold planeInteraction
  apply Finset.prod_pos
  intro e he
  exact frameInteraction_pos κ hBounds hκ (internalBond_adjacent he)
    (extendLetters σ e.1) (extendLetters σ e.2)

private lemma planeProductReference_pos {W : Finset Plane} (κ : Plane → Fin 3)
    (hBounds : interactionBounds) (hκ : ProperPlaneColouring κ)
    (η : FrameBoundary W) (σ : PlaneConfiguration W) :
    0 < planeProductReference κ W η σ := by
  unfold planeProductReference
  apply Finset.prod_pos
  intro x hx
  unfold AKLT.Defs.normalize
  apply div_pos
  · exact planeSiteWeight_pos κ hBounds hκ η x (σ x)
  · apply Finset.sum_pos
    · intro a ha
      exact planeSiteWeight_pos κ hBounds hκ η x a
    · exact Finset.univ_nonempty

private lemma boundaryProduct_regroup {W : Finset Plane} (κ : Plane → Fin 3)
    (η : FrameBoundary W) (σ : PlaneConfiguration W) :
    (∏ x : W, ∏ e ∈ (originalLegs W).filter (fun e => e.1 = x.val),
      (1 + dot (frameVector (κ e.1) (extendLetters σ e.1))
        (frameVector (κ e.2) (extendBoundary η e.2)))) =
      ∏ e ∈ originalLegs W,
        (1 + dot (frameVector (κ e.1) (extendLetters σ e.1))
          (frameVector (κ e.2) (extendBoundary η e.2))) := by
  classical
  have hfiber := Finset.prod_fiberwise_of_maps_to
    (s := originalLegs W) (t := W) (g := Prod.fst)
    (fun e he => originalLeg_source_mem he)
    (fun e => 1 + dot (frameVector (κ e.1) (extendLetters σ e.1))
      (frameVector (κ e.2) (extendBoundary η e.2)))
  exact (Finset.prod_coe_sort W _).trans hfiber

private lemma localSiteProduct_eq {W : Finset Plane} (κ : Plane → Fin 3)
    (η : FrameBoundary W) (σ : PlaneConfiguration W) :
    (∏ x : W, planeSiteWeight κ W η x (σ x)) =
      (1 / 12 : ℝ) ^ W.card *
        ∏ e ∈ originalLegs W,
          (1 + dot (frameVector (κ e.1) (extendLetters σ e.1))
            (frameVector (κ e.2) (extendBoundary η e.2))) := by
  unfold planeSiteWeight
  rw [Finset.prod_mul_distrib]
  have hterms : ∀ x : W,
      (∏ e ∈ (originalLegs W).filter (fun e => e.1 = x.val),
        (1 + dot (frameVector (κ x.val) (σ x))
          (frameVector (κ e.2) (extendBoundary η e.2)))) =
      ∏ e ∈ (originalLegs W).filter (fun e => e.1 = x.val),
        (1 + dot (frameVector (κ e.1) (extendLetters σ e.1))
          (frameVector (κ e.2) (extendBoundary η e.2))) := by
    intro x
    apply Finset.prod_congr rfl
    intro e he
    have hsrc := (Finset.mem_filter.mp he).2
    have hext : extendLetters σ e.1 = σ x := by
      simp [extendLetters, hsrc, x.property]
    rw [← hsrc, hext]
  calc
    _ = (∏ x : W, (1 / 12 : ℝ)) *
        ∏ x : W, ∏ e ∈ (originalLegs W).filter (fun e => e.1 = x.val),
          (1 + dot (frameVector (κ x.val) (σ x))
            (frameVector (κ e.2) (extendBoundary η e.2))) := rfl
    _ = (∏ x : W, (1 / 12 : ℝ)) *
        ∏ x : W, ∏ e ∈ (originalLegs W).filter (fun e => e.1 = x.val),
          (1 + dot (frameVector (κ e.1) (extendLetters σ e.1))
            (frameVector (κ e.2) (extendBoundary η e.2))) := by
          congr 1
          apply Finset.prod_congr rfl
          intro x hx
          exact hterms x
    _ = (1 / 12 : ℝ) ^ W.card *
        ∏ e ∈ originalLegs W,
          (1 + dot (frameVector (κ e.1) (extendLetters σ e.1))
            (frameVector (κ e.2) (extendBoundary η e.2))) := by
          rw [boundaryProduct_regroup]
          simp

private lemma planeWeight_factorization {W : Finset Plane} (κ : Plane → Fin 3)
    (η : FrameBoundary W) (σ : PlaneConfiguration W) :
    planeWeight κ W η σ =
      (∏ x : W, planeSiteWeight κ W η x (σ x)) * planeInteraction κ W σ := by
  rw [localSiteProduct_eq]
  unfold planeWeight planeInteraction
  ring

private lemma normalize_scaled {Ω : Type} [Fintype Ω] (c : ℝ) (w : Ω → ℝ)
    (hc : c ≠ 0) (hw : (∑ x, w x) ≠ 0) :
    normalize (fun x => c * w x) = normalize w := by
  funext x
  unfold AKLT.Defs.normalize
  rw [← Finset.mul_sum]
  field_simp [hc, hw]

theorem main : AKLT.Blueprint.Q.BoundaryAbsorptionStatement := by
  classical
  intro hBounds κ hκ W η
  let C : ℝ := ∏ x : W, siteNormalizer κ η x
  have hCpos : 0 < C := by
    dsimp [C]
    apply Finset.prod_pos
    intro x hx
    exact siteNormalizer_pos κ hBounds hκ η x
  have hreferenceFactor (σ : PlaneConfiguration W) :
      C * planeProductReference κ W η σ =
        ∏ x : W, planeSiteWeight κ W η x (σ x) := by
    dsimp [C, planeProductReference]
    unfold AKLT.Defs.normalize
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro x hx
    have hn : siteNormalizer κ η x ≠ 0 :=
      ne_of_gt (siteNormalizer_pos κ hBounds hκ η x)
    have hn' : (∑ a : IcoLetter, planeSiteWeight κ W η x a) ≠ 0 := by
      simpa [siteNormalizer] using hn
    dsimp [siteNormalizer]
    change (∑ a : IcoLetter, planeSiteWeight κ W η x a) *
        (planeSiteWeight κ W η x (σ x) /
          (∑ a : IcoLetter, planeSiteWeight κ W η x a)) = _
    calc
      _ = (∑ a : IcoLetter, planeSiteWeight κ W η x a) *
          (planeSiteWeight κ W η x (σ x) *
            (∑ a : IcoLetter, planeSiteWeight κ W η x a)⁻¹) := by
            rw [div_eq_mul_inv]
      _ = planeSiteWeight κ W η x (σ x) *
          ((∑ a : IcoLetter, planeSiteWeight κ W η x a) *
            (∑ a : IcoLetter, planeSiteWeight κ W η x a)⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hn', mul_one]
  have hscaled (σ : PlaneConfiguration W) :
      planeWeight κ W η σ = C *
        (planeProductReference κ W η σ * planeInteraction κ W σ) := by
    rw [planeWeight_factorization, ← hreferenceFactor]
    ring
  have hwpos : ∀ σ : PlaneConfiguration W,
      0 < planeProductReference κ W η σ * planeInteraction κ W σ := by
    intro σ
    exact mul_pos (planeProductReference_pos κ hBounds hκ η σ)
      (planeInteraction_pos κ hBounds hκ σ)
  have hsum : 0 < ∑ σ : PlaneConfiguration W,
      planeProductReference κ W η σ * planeInteraction κ W σ :=
    Finset.sum_pos (fun σ _ => hwpos σ) Finset.univ_nonempty
  have hnorm := normalize_scaled C
    (fun σ : PlaneConfiguration W => planeProductReference κ W η σ * planeInteraction κ W σ)
    (ne_of_gt hCpos) (ne_of_gt hsum)
  funext σ
  change normalize (planeWeight κ W η) σ =
    normalize (fun τ => planeProductReference κ W η τ * planeInteraction κ W τ) σ
  rw [show planeWeight κ W η = fun τ => C *
      (planeProductReference κ W η τ * planeInteraction κ W τ) from by
        funext τ
        exact hscaled τ]
  exact congrFun hnorm σ

end AKLT.W.Q057

