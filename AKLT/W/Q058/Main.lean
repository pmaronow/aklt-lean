module
public import AKLT.Blueprint.Q.NodesEnergy

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs
open AKLT.Blueprint.Q

namespace AKLT.W.Q058

theorem main : AKLT.Blueprint.Q.PlaneDensityBoundsStatement := by
  classical
  intro hBounds κ hκ W η hprob habs
  have hsqrt : Real.sqrt 5 < 5 := by
    have hsq : Real.sqrt 5 * Real.sqrt 5 = 5 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
    have hnonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
    nlinarith
  have hb : 0 < frameBound := by
    unfold frameBound
    nlinarith
  have hb1 : frameBound < 1 := by
    unfold frameBound
    have hnonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
    nlinarith
  have hd : 0 < 2 - frameBound := by linarith

  have hbond : ∀ e ∈ internalBonds W, Adjacent e.1 e.2 := by
    intro e he
    simp only [internalBonds, Finset.mem_biUnion] at he
    rcases he with ⟨x, hxW, he⟩
    simp only [Finset.mem_image] at he
    rcases he with ⟨y, hy, rfl⟩
    have hypos : y ∈ positiveNeighbors x := (Finset.mem_inter.mp hy).1
    simp only [positiveNeighbors, Finset.mem_insert, Finset.mem_singleton] at hypos
    rcases hypos with hy | hy
    · subst y
      norm_num [Adjacent, latticeDist]
    · subst y
      norm_num [Adjacent, latticeDist]

  have hmean : 0 < planeInteractionMean κ W η := by
    unfold planeInteractionMean
    apply Finset.sum_pos
    · intro σ _
      apply mul_pos (hprob.1 σ)
      have hprod : frameBound ^ (internalBonds W).card ≤ planeInteraction κ W σ := by
        rw [planeInteraction]
        calc
          frameBound ^ (internalBonds W).card =
              ∏ e ∈ internalBonds W, frameBound := by simp
          _ ≤ ∏ e ∈ internalBonds W,
              (1 + dot (frameVector (κ e.1) (extendLetters σ e.1))
                (frameVector (κ e.2) (extendLetters σ e.2))) := by
                apply Finset.prod_le_prod₀
                · intro e he
                  exact le_of_lt hb
                · intro e he
                  exact (hBounds (κ e.1) (κ e.2) (hκ e.1 e.2 (hbond e he)
                    ) (extendLetters σ e.1) (extendLetters σ e.2)).1
      exact lt_of_lt_of_le (pow_pos hb _) hprod
    · exact Finset.univ_nonempty

  have hbounds : ∀ σ : PlaneConfiguration W,
      frameBound ^ (internalBonds W).card ≤ planeInteraction κ W σ ∧
      planeInteraction κ W σ ≤ (2 - frameBound) ^ (internalBonds W).card := by
    intro σ
    constructor
    · rw [planeInteraction]
      calc
        frameBound ^ (internalBonds W).card =
            ∏ e ∈ internalBonds W, frameBound := by simp
        _ ≤ ∏ e ∈ internalBonds W,
            (1 + dot (frameVector (κ e.1) (extendLetters σ e.1))
              (frameVector (κ e.2) (extendLetters σ e.2))) := by
              apply Finset.prod_le_prod₀
              · intro e he
                have hi := (hBounds (κ e.1) (κ e.2)
                  (hκ e.1 e.2 (hbond e he)) (extendLetters σ e.1) (extendLetters σ e.2)).1
                linarith
              · intro e he
                exact (hBounds (κ e.1) (κ e.2)
                  (hκ e.1 e.2 (hbond e he)) (extendLetters σ e.1) (extendLetters σ e.2)).1
    · rw [planeInteraction]
      calc
        ∏ e ∈ internalBonds W,
            (1 + dot (frameVector (κ e.1) (extendLetters σ e.1))
              (frameVector (κ e.2) (extendLetters σ e.2))) ≤
            ∏ e ∈ internalBonds W, (2 - frameBound) := by
              apply Finset.prod_le_prod₀
              · intro e he
                have hi := (hBounds (κ e.1) (κ e.2)
                  (hκ e.1 e.2 (hbond e he)) (extendLetters σ e.1) (extendLetters σ e.2)).1
                linarith
              · intro e he
                exact (hBounds (κ e.1) (κ e.2)
                  (hκ e.1 e.2 (hbond e he)) (extendLetters σ e.1) (extendLetters σ e.2)).2.1
        _ = (2 - frameBound) ^ (internalBonds W).card := by simp

  have hformula : ∀ σ : PlaneConfiguration W,
      planeLaw κ W η σ =
        (planeProductReference κ W η σ * planeInteraction κ W σ) /
          planeInteractionMean κ W η := by
    intro σ
    rw [habs]
    simp [AKLT.Defs.normalize, planeInteractionMean]

  have hlo_pos : 0 < planeDensityLower κ W η := by
    unfold planeDensityLower
    exact div_pos (pow_pos hb _) hmean
  have hup_pos : 0 < planeDensityUpper κ W η := by
    unfold planeDensityUpper
    exact div_pos (pow_pos hd _) hmean

  refine ⟨hmean, hlo_pos, hup_pos, ?_, ?_, ?_⟩
  · intro σ
    rw [hformula σ]
    have hnum := mul_le_mul_of_nonneg_left (hbounds σ).1 (le_of_lt (hprob.1 σ))
    change (frameBound ^ (internalBonds W).card / planeInteractionMean κ W η) *
        planeProductReference κ W η σ ≤
      (planeProductReference κ W η σ * planeInteraction κ W σ) /
        planeInteractionMean κ W η
    calc
      (frameBound ^ (internalBonds W).card / planeInteractionMean κ W η) *
          planeProductReference κ W η σ =
        (planeProductReference κ W η σ * frameBound ^ (internalBonds W).card) /
          planeInteractionMean κ W η := by ring
      _ ≤ (planeProductReference κ W η σ * planeInteraction κ W σ) /
          planeInteractionMean κ W η := by
        exact div_le_div_of_nonneg_right (by simpa [mul_comm] using hnum) hmean.le
  · intro σ
    rw [hformula σ]
    have hnum := mul_le_mul_of_nonneg_left (hbounds σ).2 (le_of_lt (hprob.1 σ))
    change (planeProductReference κ W η σ * planeInteraction κ W σ) /
        planeInteractionMean κ W η ≤
      ((2 - frameBound) ^ (internalBonds W).card / planeInteractionMean κ W η) *
        planeProductReference κ W η σ
    calc
      (planeProductReference κ W η σ * planeInteraction κ W σ) /
          planeInteractionMean κ W η ≤
        (planeProductReference κ W η σ * (2 - frameBound) ^ (internalBonds W).card) /
          planeInteractionMean κ W η :=
            div_le_div_of_nonneg_right hnum hmean.le
      _ = ((2 - frameBound) ^ (internalBonds W).card / planeInteractionMean κ W η) *
          planeProductReference κ W η σ := by ring
  · unfold planeDensityLower planeDensityUpper frameRatio
    have hmne : planeInteractionMean κ W η ≠ 0 := ne_of_gt hmean
    have hdne : 2 - frameBound ≠ 0 := ne_of_gt hd
    field_simp [hmne, hdne]
    rw [div_eq_mul_inv, mul_pow]
    have hcancel : ((2 - frameBound)⁻¹) ^ (internalBonds W).card *
        (2 - frameBound) ^ (internalBonds W).card = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hdne, one_pow]
    calc
      frameBound ^ (internalBonds W).card =
          frameBound ^ (internalBonds W).card * 1 := by simp
      _ = frameBound ^ (internalBonds W).card *
          (((2 - frameBound)⁻¹) ^ (internalBonds W).card *
            (2 - frameBound) ^ (internalBonds W).card) := by rw [hcancel]
      _ = frameBound ^ (internalBonds W).card *
          ((2 - frameBound)⁻¹) ^ (internalBonds W).card *
            (2 - frameBound) ^ (internalBonds W).card := by ac_rfl
      _ = (2 - frameBound) ^ (internalBonds W).card *
          (frameBound ^ (internalBonds W).card *
            ((2 - frameBound)⁻¹) ^ (internalBonds W).card) := by ac_rfl

end AKLT.W.Q058
