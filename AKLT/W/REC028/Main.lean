import AKLT.Blueprint.Rec.NodesLogMean
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC028

private lemma artanh_eight_upper {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Real.log ((1 + t) / (1 - t)) ≤
      2 * ∑ k ∈ Finset.range 8, t ^ (2 * k + 1) / (2 * k + 1 : ℝ) +
        2 * t ^ 17 / (17 * (1 - t ^ 2)) := by
  have hden : 0 < 1 - t ^ 2 := by nlinarith [sq_nonneg t]
  let F : ℝ → ℝ := fun x =>
    1 / 2 * Real.log ((1 + x) / (1 - x)) -
      ∑ k ∈ Finset.range 8, x ^ (2 * k + 1) / (2 * k + 1 : ℝ)
  let H : ℝ → ℝ := fun x => x ^ 17 / (17 * (1 - t ^ 2)) - F x
  have derivH (x : ℝ) (hx : x ∈ Set.Icc 0 t) :
      HasDerivAt H (x ^ 16 / (1 - t ^ 2) - x ^ 16 / (1 - x ^ 2)) x := by
    have hxI : x ∈ Set.Ioo (-1 : ℝ) 1 := by
      simp only [Set.mem_Icc] at hx
      constructor <;> linarith
    have hdF := Real.hasDerivAt_half_log_one_add_div_one_sub_sub_sum_range
      (y := x) 8 hxI.1 hxI.2
    have hdP : HasDerivAt (fun y : ℝ => y ^ 17 / (17 * (1 - t ^ 2)))
        (x ^ 16 / (1 - t ^ 2)) x := by
      have hp := (hasDerivAt_pow 17 x).div_const (17 * (1 - t ^ 2))
      convert hp using 1 <;> field_simp [hden.ne'] <;> ring
    have hdF' : HasDerivAt F (x ^ 16 / (1 - x ^ 2)) x := by
      have hpowe : (x ^ 2) ^ 8 = x ^ 16 := by ring
      simpa [F, hpowe] using hdF
    change HasDerivAt (fun y : ℝ => y ^ 17 / (17 * (1 - t ^ 2)) - F y)
      (x ^ 16 / (1 - t ^ 2) - x ^ 16 / (1 - x ^ 2)) x
    exact hdP.sub hdF'
  have hmono : MonotoneOn H (Set.Icc 0 t) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 t) (f := H)
      (f' := fun x => x ^ 16 / (1 - t ^ 2) - x ^ 16 / (1 - x ^ 2)) ?_ ?_ ?_
    · intro x hx
      exact (derivH x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (by
        exact (derivH x (interior_subset hx)).hasDerivWithinAt)
    · intro x hx
      have hxI : x ∈ Set.Ioo (0 : ℝ) t := by
        simpa [interior_Icc] using hx
      have hxle : x ≤ t := hxI.2.le
      have hx2 : x ^ 2 ≤ t ^ 2 := by
        have htpos : 0 ≤ t := le_trans hxI.1.le hxle
        have hsum : 0 ≤ t + x := add_nonneg htpos hxI.1.le
        have hmul := mul_nonneg (sub_nonneg.mpr hxle) hsum
        nlinarith
      have hxd : 0 < 1 - x ^ 2 := by nlinarith
      have hx16 : 0 ≤ x ^ 16 := by positivity
      have hinv : 0 ≤ (1 : ℝ) / (1 - t ^ 2) - 1 / (1 - x ^ 2) := by
        have h := div_nonneg (sub_nonneg.mpr hx2) (mul_nonneg hden.le hxd.le)
        have hh : 1 / (1 - t ^ 2) - 1 / (1 - x ^ 2) =
            (t ^ 2 - x ^ 2) / ((1 - t ^ 2) * (1 - x ^ 2)) := by
          field_simp [hden.ne', hxd.ne']
          ring
        rw [hh]
        exact h
      have hd := mul_nonneg hx16 hinv
      have hder : x ^ 16 / (1 - t ^ 2) - x ^ 16 / (1 - x ^ 2) =
          x ^ 16 * ((1 : ℝ) / (1 - t ^ 2) - 1 / (1 - x ^ 2)) := by ring
      rw [hder]
      exact hd
  have hmono' : H 0 ≤ H t := hmono ⟨le_rfl, ht0⟩ ⟨ht0, le_rfl⟩ ht0
  have hFzero : F 0 = 0 := by simp [F]
  have hbound : F t ≤ t ^ 17 / (17 * (1 - t ^ 2)) := by
    simp [H, hFzero] at hmono'
    linarith
  dsimp [F] at hbound
  have hbound' : (1 / 2 : ℝ) * Real.log ((1 + t) / (1 - t)) ≤
      (∑ k ∈ Finset.range 8, t ^ (2 * k + 1) / (2 * k + 1 : ℝ)) +
        t ^ 17 / (17 * (1 - t ^ 2)) := by linarith
  calc
    Real.log ((1 + t) / (1 - t)) =
        2 * ((1 / 2 : ℝ) * Real.log ((1 + t) / (1 - t))) := by ring
    _ ≤ 2 * ((∑ k ∈ Finset.range 8, t ^ (2 * k + 1) / (2 * k + 1 : ℝ)) +
          t ^ 17 / (17 * (1 - t ^ 2))) :=
      mul_le_mul_of_nonneg_left hbound' (by norm_num)
    _ = 2 * ∑ k ∈ Finset.range 8, t ^ (2 * k + 1) / (2 * k + 1 : ℝ) +
          2 * t ^ 17 / (17 * (1 - t ^ 2)) := by ring

private lemma reciprocal_log_mean_eq {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    reciprocalLogMean s = -Real.log s / (1 - s) := by
  have hlog : Real.log s < 0 := Real.log_neg hs0 hs1
  have hlogs : Real.log s ≠ 0 := hlog.ne
  have hne : s ≠ 1 := ne_of_lt hs1
  simp only [reciprocalLogMean, logarithmicMean, if_neg hne, Real.log_one, sub_zero]
  rw [inv_div]
  field_simp [hlogs, hne]
  <;> ring

theorem main : AKLT.Blueprint.Rec.LogEnclosureUpperStatement := by
  intro s hs0 hs1
  let x : ℝ := s
  let tq : ℚ := (1 - s) / (1 + s)
  let t : ℝ := tq
  have hx0 : 0 < x := by dsimp [x]; exact_mod_cast hs0
  have hx1 : x < 1 := by dsimp [x]; exact_mod_cast hs1
  have htformula : t = (1 - x) / (1 + x) := by
    dsimp [t, tq, x]
    norm_cast
  have ht0 : 0 ≤ t := by
    rw [htformula]
    positivity
  have ht1 : t < 1 := by
    rw [htformula]
    rw [div_lt_one (by linarith : 0 < 1 + x)]
    linarith
  have hratio : (1 + t) / (1 - t) = 1 / x := by
    rw [htformula]
    have hxden : 1 + x ≠ 0 := by linarith
    have hxnum : 1 + x - (1 - x) ≠ 0 := by
      convert (mul_pos (by norm_num : (0 : ℝ) < 2) hx0).ne' using 1 <;> ring
    field_simp [hxden, hxnum]
    <;> ring
  have hlogratio : Real.log ((1 + t) / (1 - t)) = -Real.log x := by
    rw [hratio, one_div, Real.log_inv]
  have hseries : Real.log ((1 + t) / (1 - t)) ≤
      2 * ∑ k ∈ Finset.range 8, t ^ (2 * k + 1) / (2 * k + 1 : ℝ) +
        2 * t ^ 17 / (17 * (1 - t ^ 2)) := artanh_eight_upper ht0 ht1
  have hnum : -Real.log x ≤
      2 * ∑ k ∈ Finset.range 8, t ^ (2 * k + 1) / (2 * k + 1 : ℝ) +
        2 * t ^ 17 / (17 * (1 - t ^ 2)) := by
    rw [← hlogratio]
    exact hseries
  have hdiv := div_le_div_of_nonneg_right hnum (le_of_lt (sub_pos.mpr hx1))
  have hrec := reciprocal_log_mean_eq hx0 hx1
  rw [hrec]
  have hcast : (logMeanUpper s : ℝ) =
      (2 * ∑ k ∈ Finset.range 8, t ^ (2 * k + 1) / (2 * k + 1 : ℝ) +
        2 * t ^ 17 / (17 * (1 - t ^ 2))) / (1 - x) := by
    dsimp [logMeanUpper, logMeanLower, t, tq, x]
    push_cast
    have hsne : (1 : ℝ) - (s : ℝ) ≠ 0 := by
      intro h
      have hsEq : (s : ℝ) = 1 := by linarith
      have hslt : (s : ℝ) < 1 := by exact_mod_cast hs1
      exact (ne_of_lt hslt) hsEq
    have hsplus : (1 : ℝ) + s ≠ 0 := by positivity
    have htden : (1 : ℝ) - ((1 - s) / (1 + s) : ℝ) ^ 2 ≠ 0 := by
      have ht' : ((1 - s) / (1 + s) : ℝ) < 1 := by
        rw [div_lt_one (by positivity : (0 : ℝ) < 1 + s)]
        have hs0' : (0 : ℝ) < s := by exact_mod_cast hs0
        linarith
      have ht'' : 0 ≤ ((1 - s) / (1 + s) : ℝ) := by positivity
      nlinarith [sq_nonneg ((1 - s) / (1 + s) : ℝ)]
    field_simp [hsne, hsplus, htden]
  rw [hcast]
  convert hdiv using 1

end AKLT.W.REC028

#print axioms AKLT.W.REC028.main
