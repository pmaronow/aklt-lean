module
public import AKLT.Blueprint.H3.NodesDomination
public import AKLT.Blueprint.H3.Positivity

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open AKLT.Defs AKLT.Blueprint.H3

namespace AKLT.W.H3M016

private theorem phaseTransition_mono_reward (k : StepKind) {r s : ℚ} (hrs : r ≤ s)
    (φ ψ : Phase) :
    phaseTransition k r φ ψ ≤ phaseTransition k s φ ψ := by
  cases k <;> cases φ <;> cases ψ <;>
    simp [phaseTransition] <;>
    nlinarith [mul_le_mul_of_nonneg_left hrs (passageFactor_pos true).le,
      mul_le_mul_of_nonneg_left hrs (passageFactor_pos false).le]

private theorem revisit_le_nonrevisit (k : StepKind) (hk : k ≠ .revisit)
    (r : ℚ) (hr : 0 ≤ r) (φ ψ : Phase) :
    phaseTransition .revisit 0 φ ψ ≤ phaseTransition k r φ ψ := by
  by_cases hdiag : φ = ψ
  · subst ψ
    cases k with
    | revisit => exact (hk rfl).elim
    | straight =>
        cases φ <;>
          norm_num [phaseTransition, phaseDiagonal, passageFactor, localThreshold]
    | turn =>
        cases φ <;>
          norm_num [phaseTransition, phaseDiagonal, passageFactor, localThreshold]
  · have hz : phaseTransition .revisit 0 φ ψ = 0 := by
      simp [phaseTransition, hdiag]
    rw [hz]
    exact phaseTransition_nonneg k r hr φ ψ

/-- The local coefficient comparison for every correct ten-step quotient. -/
theorem main : AKLT.Blueprint.H3.LocalCoefficientComparisonStatement := by
  intro Q hQ X d₀ n w i hFacts φ ψ
  rcases hFacts with
    ⟨hraw, hadmissible, hArrival, hWindowRevisit, hWindowFirst,
      hReward, hxCentre, hxTarget, hxNextCentre, hKnown⟩
  let win := AKLT.Blueprint.H3.suffixWindow w i.val
  let x := wordVertex kernelStart w i.val
  let a := Q.project win
  have hlabels := hQ.2 win hraw (w i)
  have hallowed : Q.allowed a (w i) = true := hlabels.1.mpr hadmissible
  rcases hlabels.2 hadmissible with ⟨hkind, _hsuccessor, hquotientArrival⟩
  by_cases hknown : x = kernelStart ∨ x = kernelStart + d₀.step
  · rcases hKnown hknown with ⟨htrueRevisit, hnotWindowRevisit, hnotKnownBond⟩
    have hnotQuotientRevisit : Q.kind a (w i) ≠ .revisit := by
      rw [hkind]
      exact hnotWindowRevisit
    unfold truePhaseCoefficient
    rw [htrueRevisit]
    simp [stationaryCoefficient, x, a, win, hxCentre, hxTarget, hallowed,
      hknown, hnotKnownBond, hnotQuotientRevisit, phaseTransition, phaseDiagonal]
  · by_cases htrueRevisit : wordRevisit kernelStart w i = true
    · by_cases hwindowRevisit : windowKind win (w i) = .revisit
      · have hquotientRevisit : Q.kind a (w i) = .revisit := by
          rw [hkind, hwindowRevisit]
        unfold truePhaseCoefficient
        rw [htrueRevisit]
        simp [stationaryCoefficient, x, a, win, hxCentre, hxTarget, hxNextCentre,
          hallowed, hknown, hquotientRevisit, phaseTransition]
      · have hquotientNotRevisit : Q.kind a (w i) ≠ .revisit := by
          rw [hkind]
          exact hwindowRevisit
        have hrelaxedNonneg :
            0 ≤ relaxedReward x (Q.arrival a) (w i) {kernelCentre} :=
          relaxedReward_nonneg _ _ _ _
        have hstationary : stationaryCoefficient Q X d₀ φ a x (w i) ψ =
            phaseTransition (Q.kind a (w i))
              (relaxedReward x (Q.arrival a) (w i) {kernelCentre}) φ ψ := by
          simp [stationaryCoefficient, x, a, win, hxCentre, hxTarget, hxNextCentre,
            hallowed, hknown]
        by_cases hdiag : φ = ψ
        · subst ψ
          have htrueCoeff : truePhaseCoefficient w i φ φ = 1 / 5 := by
            simp [truePhaseCoefficient, htrueRevisit, phaseTransition, phaseDiagonal]
          rw [htrueCoeff, hstationary]
          simpa [phaseTransition, phaseDiagonal] using
            (revisit_le_nonrevisit (Q.kind a (w i)) hquotientNotRevisit _
              hrelaxedNonneg φ φ)
        · have htrueCoeff : truePhaseCoefficient w i φ ψ = 0 := by
            simp [truePhaseCoefficient, htrueRevisit, phaseTransition, hdiag]
          rw [htrueCoeff]
          exact stationaryCoefficient_nonneg Q X d₀ φ a x (w i) ψ
    · have htrueNotRevisit : wordRevisit kernelStart w i = false := by
        cases hvalue : wordRevisit kernelStart w i <;> simp_all
      have hwindowFirst := hWindowFirst htrueNotRevisit
      have htrueKindNotRevisit : trueKind w i ≠ .revisit := by
        cases hstraight : wordStraight kernelIncoming w i <;>
          simp [trueKind, htrueNotRevisit, hstraight]
      have hwindowNotRevisit : windowKind win (w i) ≠ .revisit := by
        rw [hwindowFirst]
        exact htrueKindNotRevisit
      have hquotientKind : Q.kind a (w i) = trueKind w i := by
        rw [hkind, hwindowFirst]
      have harrival : Q.arrival a = wordIncoming kernelIncoming w i := by
        calc
          Q.arrival a = windowArrival win := hquotientArrival hwindowNotRevisit
          _ = wordIncoming kernelIncoming w i := hArrival
      have hstationary : stationaryCoefficient Q X d₀ φ a x (w i) ψ =
          phaseTransition (trueKind w i)
            (relaxedReward x (wordIncoming kernelIncoming w i) (w i) {kernelCentre}) φ ψ := by
        simp [stationaryCoefficient, x, a, win, hxCentre, hxTarget, hxNextCentre,
          hallowed, hknown, hquotientKind, harrival]
      rw [show truePhaseCoefficient w i φ ψ =
          phaseTransition (trueKind w i) (witnessKappa w i) φ ψ by
            simp [truePhaseCoefficient, htrueNotRevisit, trueKind]]
      rw [hstationary]
      exact phaseTransition_mono_reward (trueKind w i) hReward φ ψ

end AKLT.W.H3M016

#print axioms AKLT.W.H3M016.main
