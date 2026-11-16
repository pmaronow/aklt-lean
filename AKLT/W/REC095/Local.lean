import AKLT.W.REC095.Pointwise

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC095

/-- A shared nonnegative local mixture would discharge the remaining local
ratio input. This implication does not assume a proof of the mixture leaf. -/
theorem coveredRatio_of_localMixture (hmixture : LocalMixtureStatementV2) :
    Residual_CoveredRatio := by
  intro hH1 a hU incoming outgoing ho hc
  obtain ⟨k, π, m, weight, hw, hcur, hnext⟩ := hmixture a hU incoming outgoing ho hc
  let c : ℝ := localThreshold (decide (outgoing = incoming))
  have hcpos : 0 < c := by
    by_cases h : outgoing = incoming <;> norm_num [c, localThreshold, h]
  have hlocal (i : Fin k) : c * patternNext (π i) (m i) ≤ patternCurrent (π i) (m i) := by
    have h := hH1.2.2.2.2 (π i) (hw i).2.1 (m i)
    have htype : (if (π i).outgoing = .north then (961 / 1000 : ℝ) else 187 / 200) = c := by
      by_cases hd : outgoing = incoming
      · have hn : (π i).outgoing = .north := (hw i).2.2.mpr hd
        simp [hn, c, localThreshold, hd]
      · have hn : (π i).outgoing ≠ .north := fun hn => hd ((hw i).2.2.mp hn)
        simp [hn, c, localThreshold, hd]
    rwa [htype] at h
  have hint : c * (traceStep a.D a.y a.o).partition a.τ true (fun _ => 1) ≤
      a.D.partition a.τ true (fun _ => 1) := by
    rw [hcur, hnext, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    calc
      c * (weight i * patternNext (π i) (m i)) =
          weight i * (c * patternNext (π i) (m i)) := by ring
      _ ≤ weight i * patternCurrent (π i) (m i) :=
        mul_le_mul_of_nonneg_left (hlocal i) (hw i).1
  have hpos := AKLT.W.REC010.partition_pos a.D a.τ a.auxiliary true
  change (traceStep a.D a.y a.o).partition a.τ true (fun _ => 1) /
    a.D.partition a.τ true (fun _ => 1) ≤ _
  rw [passageFactor, Rat.cast_inv]
  change _ ≤ c⁻¹
  apply (div_le_iff₀ hpos).mpr
  calc
    (traceStep a.D a.y a.o).partition a.τ true (fun _ => 1) =
        c⁻¹ * (c * (traceStep a.D a.y a.o).partition a.τ true (fun _ => 1)) := by
      rw [← mul_assoc, inv_mul_cancel₀ hcpos.ne', one_mul]
    _ ≤ c⁻¹ * a.D.partition a.τ true (fun _ => 1) :=
      mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hcpos.le)

end AKLT.W.REC095
