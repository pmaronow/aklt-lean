import AKLT.W.REC089.Main
import AKLT.W.REC001.Main
import AKLT.W.REC002.Main
import AKLT.W.REC003.Main
import AKLT.W.REC004.Main
import AKLT.W.REC005.Main
import AKLT.W.REC015.Main
import AKLT.W.REC018.Main
import AKLT.W.REC020.Main
import AKLT.W.REC027.Main
import AKLT.W.REC028.Main
import AKLT.W.REC034.Main
import AKLT.W.REC035.Main
import AKLT.W.REC036.Main

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC079

/-- Apply H1 to the common nonnegative mixture, with the actual turn type. -/
theorem covered_partition_bound (hH1 : AKLT.Blueprint.Top.H1Statement)
    (a : Departure) (hU : a.D.status a.y = .U) (incoming outgoing : Compass)
    (ho : a.o = a.y + outgoing.step)
    (hcov : AKLT.Defs.CoveredDepartureV2 a.D a.y incoming outgoing) :
    (localThreshold (decide (outgoing = incoming)) : ℝ) *
      (traceStep a.D a.y a.o).partition a.τ true (fun _ => 1) ≤
        a.D.partition a.τ true (fun _ => 1) := by
  classical
  obtain ⟨k, π, m, weight, hw, hpre, hpost⟩ := AKLT.W.REC089.main a hU incoming outgoing ho hcov
  rw [hpre, hpost, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h := hH1.2.2.2.2 (π i) (hw i).2.1 (m i)
  have ht : (if (π i).outgoing = .north then (961 / 1000 : ℝ) else 187 / 200) =
      (localThreshold (decide (outgoing = incoming)) : ℝ) := by
    by_cases hs : outgoing = incoming
    · simp [hs, (hw i).2.2.mpr hs, localThreshold]
    · simp [hs, mt (hw i).2.2.mp hs, localThreshold]
  rw [ht] at h
  simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left h (hw i).1

theorem covered_ratio : CoveredRatioStatementV2 := by
  intro hH1 a hU incoming outgoing ho hcov
  have h := covered_partition_bound hH1 a hU incoming outgoing ho hcov
  have hc : (0 : ℝ) < (localThreshold (decide (outgoing = incoming)) : ℝ) := by
    cases h : decide (outgoing = incoming) <;> norm_num [localThreshold]
  have hz := AKLT.W.REC001.main a.G a.τ a.D a.auxiliary true
  change (traceStep a.D a.y a.o).partition a.τ true (fun _ => 1) /
      a.D.partition a.τ true (fun _ => 1) ≤ _
  rw [passageFactor, Rat.cast_inv]
  apply (div_le_iff₀ hz).mpr
  exact (le_inv_mul_iff₀ hc).mpr h

theorem covered_integrated_lower : CoveredIntegratedLowerStatementV2 := by
  intro hH1 a hU incoming outgoing ho hcov
  have h := covered_partition_bound hH1 a hU incoming outgoing ho hcov
  have hz := AKLT.W.REC001.main a.G a.τ a.D a.auxiliary true
  constructor
  · intro f hs hne
    obtain ⟨hpre, hpost⟩ := AKLT.W.REC003.main a hU f hs hne true
    have hi := ((AKLT.W.REC005.main a hU f hs hne).1 true).1
    have hr : 0 < (removeSite a.D a.y).partition a.τ true (fun _ => 1) := by
      rw [hpre] at hz
      nlinarith
    rw [hpre, hpost] at h
    nlinarith
  · intro f g hs hof hog hfg
    obtain ⟨hpre, hpost⟩ := AKLT.W.REC002.main a hU f g hs hof hog hfg true
    have hi := ((AKLT.W.REC004.main a hU f g hs hof hog hfg).1 true).1
    have hr : 0 < (removeSite a.D a.y).partition a.τ true (fun _ => 1) := by
      rw [hpre] at hz
      nlinarith
    rw [hpre, hpost] at h
    nlinarith

/-- The repaired shared-matcher coefficient interface, derived from proved
mixture, interval, analytic and rational-enclosure leaves. -/
theorem response_typed : AKLT.Blueprint.Top.ResponseTypedStatementV2 := by
  classical
  intro hH1
  refine ⟨typedCrudeRows, ?_⟩
  intro G τ D hD y hy hU incoming outgoing hcov
  let o := y + outgoing.step
  let straight := decide (outgoing = incoming)
  have hc : (3 / 5 : ℝ) ≤ localThreshold straight ∧ (localThreshold straight : ℝ) ≤ 1 := by
    cases hs : straight <;> norm_num [localThreshold]
  have hcq : (0 : ℚ) < localThreshold straight ∧ localThreshold straight < 1 := by
    cases hs : straight <;> norm_num [localThreshold]
  have hca : (0 : ℚ) < (116 / 125) * localThreshold straight ∧
      (116 / 125 : ℚ) * localThreshold straight < 1 := by
    cases hs : straight <;> norm_num [localThreshold]
  have eup := AKLT.W.REC028.main _ hcq.1 hcq.2
  have eaup : reciprocalLogMean ((116 / 125) * (localThreshold straight : ℝ)) ≤
      (logMeanUpper ((116 / 125) * localThreshold straight) : ℝ) := by
    simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using
      AKLT.W.REC028.main _ hca.1 hca.2
  have ealow : (logMeanLower (116 / 125) : ℝ) ≤ reciprocalLogMean (116 / 125) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using
      AKLT.W.REC027.main (116 / 125) (by norm_num) (by norm_num)
  have row := logRationalRows straight
  have rowα : (logMeanUpper ((116 / 125) * localThreshold straight) : ℝ) / 3 -
      (logMeanLower (116 / 125) : ℝ) / 5 ≤ (alphaBound straight : ℝ) := by exact_mod_cast row.1
  have rowβ : (logMeanUpper ((116 / 125) * localThreshold straight) : ℝ) / 3 ≤
      (betaBound straight : ℝ) := by exact_mod_cast row.2.1
  have rowβ' : (logMeanUpper (localThreshold straight) : ℝ) / 3 ≤
      (betaPrimeBound straight : ℝ) := by exact_mod_cast row.2.2.1
  constructor
  · intro f hs hne
    have ho : o ∈ D.presentNeighbours y := by rw [hs]; simp [o]
    let a : Departure := ⟨G, τ, D, y, o, hD, hy, ho⟩
    have low := (covered_integrated_lower hH1 a hU incoming outgoing rfl hcov).1 f hs hne
    have free := (AKLT.W.REC005.main a hU f hs hne).2
    have ana : responseBetaPrime D τ y o f ≤ reciprocalLogMean (localThreshold straight : ℝ) / 3 :=
      AKLT.W.REC034.main _ _ _ (by linarith [hc.1]) low free
    exact ⟨AKLT.W.REC015.main a hU f hs hne, by linarith, ana⟩
  · intro f g hs hof hog hfg
    have ho : o ∈ D.presentNeighbours y := by rw [hs]; simp [o]
    let a : Departure := ⟨G, τ, D, y, o, hD, hy, ho⟩
    have low := (covered_integrated_lower hH1 a hU incoming outgoing rfl hcov).2 f g hs hof hog hfg
    have ints := AKLT.W.REC004.main a hU f g hs hof hog hfg
    have anaβ : responseBeta D τ y o f g ≤
        reciprocalLogMean ((116 / 125) * (localThreshold straight : ℝ)) / 3 :=
      AKLT.W.REC035.main _ _ _ _ _ hc.1 hc.2 low ints.2.2 (ints.1 true).2.2.1 ints.2.1
    have anaα : responseAlpha D τ y o f g ≤
        reciprocalLogMean ((116 / 125) * (localThreshold straight : ℝ)) / 3 -
          reciprocalLogMean (116 / 125) / 5 :=
      AKLT.W.REC036.main _ _ _ _ _ hc.1 hc.2 low ints.2.2 (ints.1 true).2.2.1 ints.2.1
    exact ⟨AKLT.W.REC018.main a hU f g hs hof hog hfg, by linarith,
      AKLT.W.REC020.main a hU f g hs hof hog hfg, by linarith, anaβ, anaα,
      low, ints.2.2, ints.2.1, (ints.1 true).2.2.1⟩

end AKLT.W.REC079
