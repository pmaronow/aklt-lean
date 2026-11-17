module
public import AKLT.Blueprint.Win.NodesTail

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open AKLT.Defs
open AKLT.Blueprint.Win

namespace AKLT.W.WIN073

theorem main : AKLT.Blueprint.Win.TailThresholdStatement := by
  intro θ hθ hθ1 htail
  have hlog : Real.log θ < 0 := by
    calc
      Real.log θ < Real.log 1 := Real.log_lt_log hθ hθ1
      _ = 0 := by simp
  have hneglog : 0 < -Real.log θ := neg_pos.mpr hlog
  let K : ℝ := AKLT.Blueprint.Win.tailConstant θ
  have hKpos : 0 < K := by
    dsimp [K, AKLT.Blueprint.Win.tailConstant]
    positivity
  let M : ℕ := max (geometryThreshold 64) (Nat.ceil (K ^ 2))
  have hgeom : geometryThreshold 64 ≤ M := le_max_left _ _
  have hMpos : 1 ≤ M := by
    have hgeompos : 1 ≤ geometryThreshold 64 := by
      norm_num [geometryThreshold]
    exact hgeompos.trans hgeom
  refine ⟨M, hMpos, hgeom, ?_⟩
  intro u hu
  have hu1 : 1 ≤ u := le_trans hMpos hu
  have hceil : Nat.ceil (K ^ 2) ≤ u := le_trans (le_max_right _ _) hu
  have hK2u : K ^ 2 ≤ (u : ℝ) := (Nat.ceil_le).1 hceil
  have hspos : 0 < shellSpacing u := by
    unfold shellSpacing
    positivity
  have hsquare : shellSpacing u ^ 2 = Real.sqrt u := by
    unfold shellSpacing
    rw [Real.sq_sqrt (by positivity)]
  have hKsqrt : K ≤ Real.sqrt u :=
    (Real.le_sqrt hKpos.le (by positivity)).2 hK2u
  have hKspacing : K ≤ shellSpacing u ^ 2 := by
    rw [hsquare]
    exact hKsqrt
  have hdecay : K * shellSpacing u ^ (-2 : ℤ) ≤ 1 := by
    have hzpow : shellSpacing u ^ (-2 : ℤ) = (shellSpacing u ^ 2)⁻¹ := by
      rw [zpow_neg]
      simp only [zpow_ofNat]
    rw [hzpow, ← div_eq_mul_inv]
    exact (div_le_one₀ (sq_pos_of_pos hspos)).2 hKspacing
  have htail' : tailCost θ u ≤ K * shellSpacing u ^ (-2 : ℤ) := by
    simpa [K] using htail u hu1
  exact htail'.trans hdecay

#print axioms main

end AKLT.W.WIN073
