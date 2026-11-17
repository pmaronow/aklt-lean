import AKLT.W.REC090.Mixtures
import AKLT.W.REC089.Main

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC090

/-- Both normalizers are positive without any remaining proof obligation. -/
theorem positive_normalizers (a : AKLT.Blueprint.Rec.Departure) :
    0 < a.D.partition a.τ true (fun _ => 1) ∧
      0 < (traceStep a.D a.y a.o).partition a.τ true (fun _ => 1) :=
  ⟨partition_pos _ _ _, partition_pos _ _ _⟩

/-- A common nonnegative ball-field representation transfers the H1 bound
to the actual step ratio using the positive current normalizer. -/
theorem coveredRatio_of_sharedBallMixture (hMix : Residual_sharedBallMixture) :
    AKLT.Blueprint.Rec.CoveredRatioStatementV2 := by
  intro hH1 a hU incoming outgoing hyo hcov
  rcases hMix a hU incoming outgoing hyo hcov with
    ⟨k, π, b, weight, hweight, hcurrent, hnext⟩
  let c : ℝ := localThreshold (decide (outgoing = incoming))
  have hc : 0 < c := by
    dsimp [c, localThreshold]
    cases decide (outgoing = incoming) <;> norm_num
  have hterm : ∀ i : Fin k,
      c * patternBallFunctional (π i) true (b i) (fun _ => 1) ≤
        patternBallFunctional (π i) false (b i) (fun _ => 1) := by
    intro i
    have hi := h1_ball_pattern_bound hH1 (π i) (hweight i).2.1 (b i) (hweight i).2.2.1
    have htype := (hweight i).2.2.2
    by_cases hs : outgoing = incoming
    · have hnorth : (π i).outgoing = .north := htype.mpr hs
      simpa [c, localThreshold, hs, hnorth] using hi
    · have hnotnorth : (π i).outgoing ≠ .north := fun hn => hs (htype.mp hn)
      simpa [c, localThreshold, hs, hnotnorth] using hi
  have hsum : c * (∑ i : Fin k,
      weight i * patternBallFunctional (π i) true (b i) (fun _ => 1)) ≤
      ∑ i : Fin k, weight i * patternBallFunctional (π i) false (b i) (fun _ => 1) := by
    calc
      c * (∑ i, weight i * patternBallFunctional (π i) true (b i) (fun _ => 1)) =
          ∑ i, weight i * (c * patternBallFunctional (π i) true (b i) (fun _ => 1)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ ≤ ∑ i, weight i * patternBallFunctional (π i) false (b i) (fun _ => 1) := by
            apply Finset.sum_le_sum
            intro i hi
            exact mul_le_mul_of_nonneg_left (hterm i) (hweight i).1
  have hscaled : c * (traceStep a.D a.y a.o).partition a.τ true (fun _ => 1) ≤
      a.D.partition a.τ true (fun _ => 1) := by
    rw [hnext, hcurrent]
    exact hsum
  have hden : 0 < a.D.partition a.τ true (fun _ => 1) :=
    (positive_normalizers a).1
  have hquot :
      (traceStep a.D a.y a.o).partition a.τ true (fun _ => 1) /
        a.D.partition a.τ true (fun _ => 1) ≤ c⁻¹ := by
    apply (div_le_iff₀ hden).2
    calc
      (traceStep a.D a.y a.o).partition a.τ true (fun _ => 1) =
          c⁻¹ * (c * (traceStep a.D a.y a.o).partition a.τ true (fun _ => 1)) := by
            field_simp [ne_of_gt hc]
      _ ≤ c⁻¹ * a.D.partition a.τ true (fun _ => 1) :=
        mul_le_mul_of_nonneg_left hscaled (le_of_lt (inv_pos.mpr hc))
  have hfactor :
      (passageFactor (decide (outgoing = incoming)) : ℝ) = c⁻¹ := by
    simp [c, passageFactor, localThreshold]
  change traceRatio a.D a.τ true [a.y, a.o] ≤ _
  rw [show traceRatio a.D a.τ true [a.y, a.o] =
      (traceStep a.D a.y a.o).partition a.τ true (fun _ => 1) /
        a.D.partition a.τ true (fun _ => 1) by rfl]
  exact hquot.trans_eq hfactor.symm

/-- Explicit reduction to the named blueprint dependency. -/
theorem coveredRatio_of_localMixture :
    AKLT.Blueprint.Rec.LocalMixtureStatementV2 →
      AKLT.Blueprint.Rec.CoveredRatioStatementV2 := fun hMix =>
  coveredRatio_of_sharedBallMixture (sharedBallMixture_of_localMixture hMix)

/-- Apply H1 to the shared covered-pattern mixture proved in REC089,
average with its common nonnegative weights, and divide by the positive
current partition function. -/
theorem main : AKLT.Blueprint.Rec.CoveredRatioStatementV2 :=
  coveredRatio_of_localMixture AKLT.W.REC089.main

#print axioms coveredRatio_of_sharedBallMixture
#print axioms main
#print axioms coveredRatio_of_localMixture

end AKLT.W.REC090
