module
public import AKLT.Blueprint.Rec.NodesLogMean
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open Finset Set

namespace AKLT.W.REC026

theorem main : AKLT.Blueprint.Rec.EightTermRemainderStatement := by
  intro t ht0 ht1
  let F : ℝ → ℝ := fun x =>
    1 / 2 * Real.log ((1 + x) / (1 - x)) -
      ∑ k ∈ Finset.range 8, x ^ (2 * k + 1) / (2 * k + 1 : ℝ)
  let B : ℝ → ℝ := fun x => x ^ 17 / (17 * (1 - x ^ 2))
  let DB : ℝ → ℝ := fun x =>
    (17 * x ^ 16 * (17 * (1 - x ^ 2)) + x ^ 17 * (17 * (2 * x))) /
      (17 * (1 - x ^ 2)) ^ 2
  let Hderiv : ℝ → ℝ := fun x => DB x - (x ^ 2) ^ 8 / (1 - x ^ 2)
  have hF : ∀ y ∈ Icc 0 t,
      HasDerivAt F ((y ^ 2) ^ 8 / (1 - y ^ 2)) y := by
    intro y hy
    apply Real.hasDerivAt_half_log_one_add_div_one_sub_sub_sum_range
    · exact lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) hy.1
    · exact hy.2.trans_lt ht1
  have hFnonneg :
      0 ≤ Real.log ((1 + t) / (1 - t)) -
        2 * ∑ k ∈ Finset.range 8, t ^ (2 * k + 1) / (2 * k + 1 : ℝ) := by
    have hs := Real.sum_range_le_log_div (le_of_lt ht0) ht1 8
    linarith
  have hHmono : MonotoneOn (fun x => B x - F x) (Icc 0 t) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg
      (D := Icc 0 t) (f := fun x => B x - F x)
      (f' := Hderiv)
      (convex_Icc 0 t)
      (fun y hy => ?_)
      (fun y hy => ?_)
      (fun y hy => ?_)
    · have hy' : y ∈ Icc 0 t := hy
      have hf := hF y hy'
      have hylt : y < 1 := hy'.2.trans_lt ht1
      have hden : 17 * (1 - y ^ 2) ≠ 0 := by
        have hp : 0 < 1 - y ^ 2 := by
          have hprod := mul_pos (sub_pos.mpr hylt)
            (by linarith [hy'.1] : 0 < 1 + y)
          nlinarith [hprod]
        positivity
      have hBc : ContinuousAt B y := by
        dsimp [B]
        exact (continuousAt_id.pow 17).div
          (continuousAt_const.mul (continuousAt_const.sub (continuousAt_id.pow 2))) hden
      exact (hBc.sub hf.continuousAt).continuousWithinAt
    ·
      have hyI : y ∈ Icc 0 t := interior_subset hy
      have hy0 : 0 < y := by
        simp only [interior_Icc, Set.mem_Ioo] at hy
        exact hy.1
      have hy1 : y < 1 := hyI.2.trans_lt ht1
      have hden : 0 < 1 - y ^ 2 := by
        have hprod := mul_pos (sub_pos.mpr hy1) (by linarith [hyI.1] : 0 < 1 + y)
        nlinarith [hprod]
      have hh := (hF y hyI)
      have hb : HasDerivAt B (DB y) y := by
        have hden' : 17 * (1 - y ^ 2) ≠ 0 := by positivity
        have hraw := (hasDerivAt_pow 17 y).div
          ((hasDerivAt_const y (17 : ℝ)).mul
            ((hasDerivAt_const y (1 : ℝ)).sub (hasDerivAt_pow 2 y))) hden'
        convert hraw using 1
        dsimp [DB]
        norm_num [pow_succ]
      exact (hb.sub hh).hasDerivWithinAt
    ·
      have hyI : y ∈ Icc 0 t := interior_subset hy
      have hylt : y < 1 := hyI.2.trans_lt ht1
      have hy0 : 0 < y := by
        have hy' : y ∈ interior (Icc (0 : ℝ) t) := hy
        have hy'' : 0 < y ∧ y < t := by
          simpa only [interior_Icc, Set.mem_Ioo] using hy'
        exact hy''.1
      have hdenpos : 0 < 1 - y ^ 2 := by
        have hprod := mul_pos (sub_pos.mpr hylt) (by linarith : 0 < 1 + y)
        nlinarith [hprod]
      have hden : 17 * (1 - y ^ 2) ≠ 0 := by
        have hp : 0 < 1 - y ^ 2 := by
          exact hdenpos
        positivity
      have hcalc : Hderiv y = 2 * y ^ 18 / (17 * (1 - y ^ 2) ^ 2) := by
        dsimp [Hderiv, DB]
        have hp : (y ^ 2) ^ 8 = y ^ 16 := by
          rw [← pow_mul]
        rw [hp]
        field_simp [hden]
        ; ring
      rw [hcalc]
      positivity
  have hbound := hHmono ⟨le_rfl, le_of_lt ht0⟩ ⟨le_of_lt ht0, le_rfl⟩ (le_of_lt ht0)
  have hBnonneg : 0 ≤
      2 * t ^ 17 / (17 * (1 - t ^ 2)) -
        (Real.log ((1 + t) / (1 - t)) -
          2 * ∑ k ∈ Finset.range 8, t ^ (2 * k + 1) / (2 * k + 1 : ℝ)) := by
    have hzero : B 0 - F 0 = 0 := by
      simp [B, F]
    have hbound' : 0 ≤ B t - F t := by
      rw [← hzero]
      exact hbound
    have htwice : 0 ≤ 2 * (B t - F t) := mul_nonneg (by norm_num) hbound'
    have hrem :
        Real.log ((1 + t) / (1 - t)) -
          2 * ∑ k ∈ Finset.range 8, t ^ (2 * k + 1) / (2 * k + 1 : ℝ) =
          2 * F t := by
      dsimp [F]
      ring
    rw [hrem]
    calc
      0 ≤ 2 * (B t - F t) := htwice
      _ = 2 * t ^ 17 / (17 * (1 - t ^ 2)) - 2 * F t := by
        dsimp [B]
        ring
  constructor
  · exact hFnonneg
  · exact sub_nonneg.mp hBnonneg

end AKLT.W.REC026
