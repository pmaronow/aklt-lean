import AKLT.Blueprint.H3.NodesPhase

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.H3M004

open AKLT.Blueprint.H3

private def baseFactor {n : ℕ} (w : DirectionWord n) (i : Fin n) : ℚ :=
  if wordRevisit kernelStart w i then 1 / 5 else 1 / 3

private theorem acPointwise {n : ℕ} (w : DirectionWord n) (j i : Fin n)
    (hr : wordRevisit kernelStart w j = false)
    (hs : wordStraight kernelIncoming w j = false) :
    (if i.val < j.val then phaseDiagonal .A (trueKind w i)
      else if i = j then phaseTransition (trueKind w i) (witnessKappa w i) .A .C
      else phaseDiagonal .C (trueKind w i)) =
      baseFactor w i * (if i = j then witnessKappa w j else 1) *
        (if !wordRevisit kernelStart w i &&
          (wordStraight kernelIncoming w i || decide (i.val ≤ j.val))
         then passageFactor (wordStraight kernelIncoming w i) else 1) := by
  by_cases hij : i = j
  · subst i
    simp [baseFactor, hr, hs, trueKind, phaseDiagonal, phaseTransition]
    <;> ring
  · by_cases hlt : i.val < j.val
    · have hle : i ≤ j := by omega
      by_cases hri : wordRevisit kernelStart w i = true
      · by_cases hsi : wordStraight kernelIncoming w i = true <;>
          simp [hij, hlt, hle, hri, hsi, hr, hs, baseFactor, trueKind,
            phaseDiagonal, phaseTransition]
      · have hri' : wordRevisit kernelStart w i = false := by
          cases h : wordRevisit kernelStart w i <;> simp_all
        by_cases hsi : wordStraight kernelIncoming w i = true <;>
          simp [hij, hlt, hle, hri', hsi, hr, hs, baseFactor, trueKind,
            phaseDiagonal, phaseTransition] <;> ring
    · have hgt : j.val < i.val := by omega
      have hnle : ¬ i ≤ j := by omega
      by_cases hri : wordRevisit kernelStart w i = true
      · by_cases hsi : wordStraight kernelIncoming w i = true <;>
          simp [hij, hlt, hgt, hnle, hri, hsi, hr, hs, baseFactor, trueKind,
            phaseDiagonal, phaseTransition]
      · have hri' : wordRevisit kernelStart w i = false := by
          cases h : wordRevisit kernelStart w i <;> simp_all
        by_cases hsi : wordStraight kernelIncoming w i = true <;>
          simp [hij, hlt, hgt, hnle, hri', hsi, hr, hs, baseFactor, trueKind,
            phaseDiagonal, phaseTransition] <;> ring

private theorem bdPointwise {n : ℕ} (w : DirectionWord n) (j i : Fin n)
    (hr : wordRevisit kernelStart w j = false)
    (hs : wordStraight kernelIncoming w j = true) :
    (if i.val < j.val then phaseDiagonal .B (trueKind w i)
      else if i = j then phaseTransition (trueKind w i) (witnessKappa w i) .B .D
      else phaseDiagonal .D (trueKind w i)) =
      baseFactor w i * (if i = j then witnessKappa w j else 1) *
        (if !wordRevisit kernelStart w i &&
          (wordStraight kernelIncoming w i && decide (i.val ≤ j.val))
         then passageFactor (wordStraight kernelIncoming w i) else 1) := by
  by_cases hij : i = j
  · subst i
    simp [baseFactor, hr, hs, trueKind, phaseDiagonal, phaseTransition]
    <;> ring
  · by_cases hlt : i.val < j.val
    · have hle : i ≤ j := by omega
      by_cases hri : wordRevisit kernelStart w i = true
      · by_cases hsi : wordStraight kernelIncoming w i = true <;>
          simp [hij, hlt, hle, hri, hsi, hr, hs, baseFactor, trueKind,
            phaseDiagonal, phaseTransition]
      · have hri' : wordRevisit kernelStart w i = false := by
          cases h : wordRevisit kernelStart w i <;> simp_all
        by_cases hsi : wordStraight kernelIncoming w i = true <;>
          simp [hij, hlt, hle, hri', hsi, hr, hs, baseFactor, trueKind,
            phaseDiagonal, phaseTransition] <;> ring
    · have hgt : j.val < i.val := by omega
      have hnle : ¬ i ≤ j := by omega
      by_cases hri : wordRevisit kernelStart w i = true
      · by_cases hsi : wordStraight kernelIncoming w i = true <;>
          simp [hij, hlt, hgt, hnle, hri, hsi, hr, hs, baseFactor, trueKind,
            phaseDiagonal, phaseTransition]
      · have hri' : wordRevisit kernelStart w i = false := by
          cases h : wordRevisit kernelStart w i <;> simp_all
        by_cases hsi : wordStraight kernelIncoming w i = true <;>
          simp [hij, hlt, hgt, hnle, hri', hsi, hr, hs, baseFactor, trueKind,
            phaseDiagonal, phaseTransition] <;> ring

private theorem baseFactor_prod {n : ℕ} (w : DirectionWord n) :
    (∏ i : Fin n, baseFactor w i) = trailBaseWeight kernelStart w := by
  rfl

private theorem rewardFactor_prod {n : ℕ} (w : DirectionWord n) (j : Fin n) :
    (∏ i : Fin n, (if i = j then witnessKappa w j else (1 : ℚ))) = witnessKappa w j := by
  simp

private theorem acProduct {n : ℕ} (w : DirectionWord n) (j : Fin n)
    (hr : wordRevisit kernelStart w j = false)
    (hs : wordStraight kernelIncoming w j = false) :
    singleChange (trueKind w) (witnessKappa w) j .A .C =
      trailBaseWeight kernelStart w * witnessKappa w j * longMultiplier w j := by
  unfold singleChange
  calc
    (∏ i : Fin n, if i.val < j.val then phaseDiagonal .A (trueKind w i)
      else if i = j then phaseTransition (trueKind w i) (witnessKappa w i) .A .C
      else phaseDiagonal .C (trueKind w i)) =
      ∏ i : Fin n, baseFactor w i * (if i = j then witnessKappa w j else 1) *
        (if !wordRevisit kernelStart w i &&
          (wordStraight kernelIncoming w i || decide (i.val ≤ j.val))
         then passageFactor (wordStraight kernelIncoming w i) else 1) := by
          apply Finset.prod_congr rfl
          intro i hi
          exact acPointwise w j i hr hs
    _ = (∏ i : Fin n, baseFactor w i) *
        (∏ i : Fin n, if i = j then witnessKappa w j else (1 : ℚ)) *
        (∏ i : Fin n, if !wordRevisit kernelStart w i &&
          (wordStraight kernelIncoming w i || decide (i.val ≤ j.val))
         then passageFactor (wordStraight kernelIncoming w i) else 1) := by
          simp only [Finset.prod_mul_distrib]
    _ = trailBaseWeight kernelStart w * witnessKappa w j * longMultiplier w j := by
          rw [baseFactor_prod, rewardFactor_prod]
          simp [longMultiplier, hs]

private theorem bdProduct {n : ℕ} (w : DirectionWord n) (j : Fin n)
    (hr : wordRevisit kernelStart w j = false)
    (hs : wordStraight kernelIncoming w j = true) :
    singleChange (trueKind w) (witnessKappa w) j .B .D =
      trailBaseWeight kernelStart w * witnessKappa w j * longMultiplier w j := by
  unfold singleChange
  calc
    (∏ i : Fin n, if i.val < j.val then phaseDiagonal .B (trueKind w i)
      else if i = j then phaseTransition (trueKind w i) (witnessKappa w i) .B .D
      else phaseDiagonal .D (trueKind w i)) =
      ∏ i : Fin n, baseFactor w i * (if i = j then witnessKappa w j else (1 : ℚ)) *
        (if !wordRevisit kernelStart w i &&
          (wordStraight kernelIncoming w i && decide (i.val ≤ j.val))
         then passageFactor (wordStraight kernelIncoming w i) else 1) := by
          apply Finset.prod_congr rfl
          intro i hi
          exact bdPointwise w j i hr hs
    _ = (∏ i : Fin n, baseFactor w i) *
        (∏ i : Fin n, if i = j then witnessKappa w j else (1 : ℚ)) *
        (∏ i : Fin n, if !wordRevisit kernelStart w i &&
          (wordStraight kernelIncoming w i && decide (i.val ≤ j.val))
         then passageFactor (wordStraight kernelIncoming w i) else 1) := by
          simp only [Finset.prod_mul_distrib]
    _ = trailBaseWeight kernelStart w * witnessKappa w j * longMultiplier w j := by
          rw [baseFactor_prod, rewardFactor_prod]
          simp [longMultiplier, hs]

theorem main : AKLT.Blueprint.H3.SingleChangeFactorStatement := by
  intro n w j
  classical
  by_cases hr : wordRevisit kernelStart w j = true
  · have hac : singleChange (trueKind w) (witnessKappa w) j .A .C = 0 := by
      have hz : phaseTransition (trueKind w j) (witnessKappa w j) .A .C = 0 := by
        simp [trueKind, hr, phaseTransition]
      unfold singleChange
      apply Finset.prod_eq_zero (i := j)
      · simp
      · simpa [hz]
    have hbd : singleChange (trueKind w) (witnessKappa w) j .B .D = 0 := by
      have hz : phaseTransition (trueKind w j) (witnessKappa w j) .B .D = 0 := by
        simp [trueKind, hr, phaseTransition]
      unfold singleChange
      apply Finset.prod_eq_zero (i := j)
      · simp
      · simpa [hz]
    simp [longRewardTerm, hr, hac, hbd, trailBaseWeight]
  · have hr' : wordRevisit kernelStart w j = false := by
      cases h : wordRevisit kernelStart w j <;> simp_all
    by_cases hs : wordStraight kernelIncoming w j = true
    · have hac : singleChange (trueKind w) (witnessKappa w) j .A .C = 0 := by
        have hz : phaseTransition (trueKind w j) (witnessKappa w j) .A .C = 0 := by
          simp [trueKind, hr', hs, phaseTransition]
        unfold singleChange
        apply Finset.prod_eq_zero (i := j)
        · simp
        · simpa [hz]
      have hbd := bdProduct w j hr' hs
      simp [longRewardTerm, hr', hs, hac, hbd]
      <;> ring_nf
    · have hs' : wordStraight kernelIncoming w j = false := by
        cases h : wordStraight kernelIncoming w j <;> simp_all
      have hbd : singleChange (trueKind w) (witnessKappa w) j .B .D = 0 := by
        have hz : phaseTransition (trueKind w j) (witnessKappa w j) .B .D = 0 := by
          simp [trueKind, hr', hs', phaseTransition]
        unfold singleChange
        apply Finset.prod_eq_zero (i := j)
        · simp
        · simpa [hz]
      have hac := acProduct w j hr' hs'
      simp [longRewardTerm, hr', hs', hac, hbd]
      <;> ring_nf

end AKLT.W.H3M004
