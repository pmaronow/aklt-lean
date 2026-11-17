import AKLT.W.REC094.Dynamics
import AKLT.W.REC011.Main
import AKLT.W.REC012.Main
import AKLT.W.REC013.Main

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC094

theorem passageFactor_one_le (s : Bool) : 1 ≤ (passageFactor s : ℝ) := by
  cases s <;> norm_num [passageFactor, localThreshold]

theorem stepRatio_pos {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (y o : Plane) : 0 < stepRatio D τ b y o := by
  exact div_pos (partition_pos (traceStep D y o) τ b) (partition_pos D τ b)

/-- The uniform estimate for either pin choice uses only indexed, proved leaves. -/
theorem stepRatio_le_twelve_fifths (a : AKLT.Blueprint.Rec.Departure) (b : Bool) :
    stepRatio a.D a.τ b a.y a.o ≤ 12 / 5 := by
  cases b with
  | false => exact (AKLT.W.REC011.main a).trans (by norm_num)
  | true => exact AKLT.W.REC012.main a

/-- An admissible D departure has ratio exactly one, for either pin choice. -/
theorem dRatio_eq_one (a : AKLT.Blueprint.Rec.Departure)
    (hD : a.D.status a.y = .D) (b : Bool) :
    stepRatio a.D a.τ b a.y a.o = 1 := by
  cases b with
  | false => exact (AKLT.W.REC013.main a hD).2
  | true => exact (AKLT.W.REC013.main a hD).1

/-- The shared-mixture statement suffices for the covered-ratio comparison:
the common nonnegative mixture lets H1 compare the two partition sums. -/
theorem coveredRatio_of_mixture (hMix : AKLT.Blueprint.Rec.LocalMixtureStatementV2) :
    AKLT.Blueprint.Rec.CoveredRatioStatementV2 := by
  intro hH1 a hU incoming outgoing ho hcov
  obtain ⟨k, π, m, weight, hd, hcur, hnext⟩ := hMix a hU incoming outgoing ho hcov
  let c : ℝ := (localThreshold (decide (outgoing = incoming)) : ℝ)
  have hc : 0 < c := by
    dsimp [c]
    by_cases h : outgoing = incoming <;> norm_num [localThreshold, h]
  have hi (i : Fin k) : c * patternNext (π i) (m i) ≤ patternCurrent (π i) (m i) := by
    have hh := hH1.2.2.2.2 (π i) (hd i).2.1 (m i)
    have he : (if (π i).outgoing = .north then (961 / 1000 : ℝ) else 187 / 200) = c := by
      by_cases ho : outgoing = incoming
      · have hp := (hd i).2.2.mpr ho
        norm_num [c, localThreshold, ho, hp]
      · have hp : (π i).outgoing ≠ .north := fun hp => ho ((hd i).2.2.mp hp)
        norm_num [c, localThreshold, ho, hp]
    rwa [he] at hh
  have hbound : c * (traceStep a.D a.y a.o).partition a.τ true (fun _ => 1) ≤
      a.D.partition a.τ true (fun _ => 1) := by
    rw [hcur, hnext, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left (hi i) (hd i).1
  have hf : (passageFactor (decide (outgoing = incoming)) : ℝ) = 1 / c := by
    simp [passageFactor, c, one_div]
  rw [hf]
  change (traceStep a.D a.y a.o).partition a.τ true (fun _ => 1) /
    a.D.partition a.τ true (fun _ => 1) ≤ 1 / c
  exact (div_le_div_iff₀ (partition_pos a.D a.τ true) hc).2 (by
    simpa only [one_mul, mul_comm] using hbound)

#print axioms coveredRatio_of_mixture
#print axioms passageFactor_one_le
#print axioms stepRatio_pos
#print axioms stepRatio_le_twelve_fifths
#print axioms dRatio_eq_one

end AKLT.W.REC094
