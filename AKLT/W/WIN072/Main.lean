module
public import AKLT.Blueprint.Win.NodesTail

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section

namespace AKLT.W.WIN072

open AKLT.Blueprint.Win
open AKLT.Defs

/-- The polynomial prefactor is dominated by the tenth exponential term. -/
theorem main : AKLT.Blueprint.Win.TailExponentialStatement := by
  intro θ hθ hθ1 u hu
  let s : ℝ := shellSpacing u
  let c : ℝ := -Real.log θ
  let x : ℝ := c * s / 12
  have huR : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
  have hs0 : 0 ≤ s := by dsimp [s, shellSpacing]; positivity
  have hs2 : s ^ 2 = Real.sqrt (u : ℝ) := by
    dsimp [s, shellSpacing]
    exact Real.sq_sqrt (Real.sqrt_nonneg (u : ℝ))
  have hs4 : s ^ 4 = (u : ℝ) := by
    calc
      s ^ 4 = (s ^ 2) ^ 2 := by ring
      _ = (Real.sqrt (u : ℝ)) ^ 2 := by rw [hs2]
      _ = (u : ℝ) := Real.sq_sqrt (by positivity)
  have hinner : 1 ≤ Real.sqrt (u : ℝ) := by
    by_contra hn
    have hlt : Real.sqrt (u : ℝ) < 1 := lt_of_not_ge hn
    have hmul := mul_nonneg (Real.sqrt_nonneg (u : ℝ))
      (le_of_lt (sub_pos.mpr hlt))
    have hsq : (Real.sqrt (u : ℝ)) ^ 2 = (u : ℝ) :=
      Real.sq_sqrt (show 0 ≤ (u : ℝ) by positivity)
    nlinarith [hmul, hsq]
  have hs1 : 1 ≤ s := by
    by_contra hn
    have hlt : s < 1 := lt_of_not_ge hn
    have hmul := mul_nonneg hs0 (le_of_lt (sub_pos.mpr hlt))
    have hle : 0 ≤ s - s ^ 2 := by nlinarith [hmul]
    rw [hs2] at hle
    nlinarith
  have hspos : 0 < s := lt_of_lt_of_le (by norm_num) hs1
  have hc : 0 < c := by
    dsimp [c]
    linarith [Real.log_neg hθ hθ1]
  have hfact : (0 : ℝ) < (Nat.factorial 10 : ℝ) := by positivity
  have hthetaInv : θ⁻¹ = Real.exp c := by
    calc
      θ⁻¹ = (Real.exp (Real.log θ))⁻¹ := by rw [Real.exp_log hθ]
      _ = Real.exp (-Real.log θ) := by rw [← Real.exp_neg]
      _ = Real.exp c := rfl
  have hthetaPow : θ ^ (s / 12 - 1) = θ⁻¹ * Real.exp (-x) := by
    rw [Real.rpow_def_of_pos hθ]
    have hexpArg : Real.log θ * (s / 12 - 1) = c + -x := by
      dsimp [c, x]
      ring
    rw [hexpArg, Real.exp_add, hthetaInv]
  have hx : 0 < x := by
    dsimp [x]
    positivity
  have hexpSmall : Real.exp (-x) ≤ (Nat.factorial 10 : ℝ) / x ^ 10 := by
    have hpow := Real.pow_div_factorial_le_exp x (le_of_lt hx) 10
    have hpow' : x ^ 10 ≤ (Nat.factorial 10 : ℝ) * Real.exp x := by
      calc
        x ^ 10 ≤ Real.exp x * (Nat.factorial 10 : ℝ) :=
          (div_le_iff₀ hfact).mp hpow
        _ = (Nat.factorial 10 : ℝ) * Real.exp x := by ring
    have hmul : Real.exp (-x) * x ^ 10 ≤ (Nat.factorial 10 : ℝ) := by
      calc
        Real.exp (-x) * x ^ 10 ≤ Real.exp (-x) *
            ((Nat.factorial 10 : ℝ) * Real.exp x) :=
          mul_le_mul_of_nonneg_left hpow' (Real.exp_pos _).le
        _ = (Nat.factorial 10 : ℝ) *
              (Real.exp (-x) * Real.exp x) := by ring
        _ = (Nat.factorial 10 : ℝ) * Real.exp (-x + x) := by
          rw [← Real.exp_add]
        _ = (Nat.factorial 10 : ℝ) := by simp
    exact (le_div_iff₀ (pow_pos hx 10)).2 hmul
  have hpoly : (2 * (u : ℝ) + 1) ^ 2 ≤ 9 * (u : ℝ) ^ 2 := by
    have hmul := mul_nonneg (show 0 ≤ (u : ℝ) - 1 by linarith)
      (show 0 ≤ 5 * (u : ℝ) + 1 by positivity)
    nlinarith
  have hdenom : (Nat.factorial 10 : ℝ) / x ^ 10 =
      (Nat.factorial 10 : ℝ) * (12 / c) ^ 10 / s ^ 10 := by
    dsimp [x]
    field_simp [ne_of_gt hc, ne_of_gt hspos]
  have hsNeg2 : s ^ (-2 : ℤ) = (1 : ℝ) / s ^ 2 := by
    rw [zpow_neg]
    norm_num [zpow_natCast]
  have hscale : (u : ℝ) ^ 2 / s ^ 10 = s ^ (-2 : ℤ) := by
    calc
      (u : ℝ) ^ 2 / s ^ 10 = 1 / s ^ 2 := by
        rw [← hs4]
        field_simp [ne_of_gt hspos]
      _ = s ^ (-2 : ℤ) := by rw [hsNeg2]
  have hbody :
      4 * (2 * (u : ℝ) + 1) ^ 2 * (θ⁻¹ * Real.exp (-x)) ≤
        36 * θ⁻¹ * (Nat.factorial 10 : ℝ) * (12 / c) ^ 10 *
          s ^ (-2 : ℤ) := by
    calc
      4 * (2 * (u : ℝ) + 1) ^ 2 * (θ⁻¹ * Real.exp (-x)) ≤
          4 * (9 * (u : ℝ) ^ 2) * (θ⁻¹ *
            ((Nat.factorial 10 : ℝ) / x ^ 10)) := by
        gcongr
      _ = 36 * θ⁻¹ * (Nat.factorial 10 : ℝ) * (12 / c) ^ 10 *
            s ^ (-2 : ℤ) := by
        rw [hdenom]
        rw [← hscale]
        ring
  unfold tailCost tailConstant
  change 4 * (2 * (u : ℝ) + 1) ^ 2 *
      θ ^ (shellSpacing u / 12 - 1) ≤
    36 * θ⁻¹ * (Nat.factorial 10 : ℝ) *
      (12 / (-Real.log θ)) ^ 10 * (shellSpacing u) ^ (-2 : ℤ)
  rw [hthetaPow]
  simpa [c, s] using hbody

#print axioms AKLT.W.WIN072.main

end AKLT.W.WIN072
