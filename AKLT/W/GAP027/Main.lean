module
public import AKLT.Blueprint.Gap.NodesMain

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.GAP027

open AKLT.Defs

/-- The fourth-power threshold forces the fourth-root shell spacing to be at least 16. -/
theorem main : AKLT.Blueprint.Gap.ThresholdSpacingStatement := by
  intro l u hu
  have hthreshold : (16 : ℕ) ^ 4 ≤ geometryThreshold l := by
    unfold geometryThreshold
    exact Nat.pow_le_pow_left (le_max_left 16 (6 * (l + 1))) 4
  have hu16 : (16 : ℕ) ^ 4 ≤ u := hthreshold.trans hu
  have hreal : (16 : ℝ) ^ 4 ≤ (u : ℝ) := by
    exact_mod_cast hu16
  have hsqrt1 : Real.sqrt ((16 : ℝ) ^ 4) ≤ Real.sqrt (u : ℝ) :=
    Real.sqrt_le_sqrt hreal
  have hsqrt2 : Real.sqrt (Real.sqrt ((16 : ℝ) ^ 4)) ≤
      Real.sqrt (Real.sqrt (u : ℝ)) := Real.sqrt_le_sqrt hsqrt1
  have hroot : Real.sqrt (Real.sqrt ((16 : ℝ) ^ 4)) = 16 := by
    norm_num [Real.sqrt_sq_eq_abs]
  change (16 : ℝ) ≤ Real.sqrt (Real.sqrt (u : ℝ))
  rw [← hroot]
  exact hsqrt2

end AKLT.W.GAP027
