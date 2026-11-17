module
public import AKLT.Blueprint.Rec.NodesLogMean
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open MeasureTheory
open AKLT.Defs

namespace AKLT.W.REC025

private lemma reciprocal_logarithmicMean_integral {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) :
    (logarithmicMean r s)⁻¹ =
      ∫ t in (0 : ℝ)..1, ((1 - t) * r + t * s)⁻¹ := by
  by_cases hrs : r = s
  · subst s
    have hpoint : ∀ t : ℝ, ((1 - t) * r + t * r)⁻¹ = r⁻¹ := by
      intro t
      congr 1
      ring
    rw [intervalIntegral.integral_congr (fun t _ => hpoint t)]
    simp [logarithmicMean]
  · have hdiff : s - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hrs)
    have hpoint : ∀ t : ℝ, ((1 - t) * r + t * s)⁻¹ = (r + (s - r) * t)⁻¹ := by
      intro t
      congr 1
      ring
    rw [intervalIntegral.integral_congr (fun t _ => hpoint t)]
    rw [intervalIntegral.integral_comp_add_mul (f := fun x : ℝ => x⁻¹) hdiff r]
    simp only [smul_eq_mul]
    have hendpoints : r + (s - r) * 0 = r ∧ r + (s - r) * 1 = s := by
      constructor <;> ring
    rw [hendpoints.1, hendpoints.2, integral_inv_of_pos hr hs]
    have hlog : Real.log r ≠ Real.log s := by
      intro heq
      exact hrs (Real.log_injOn_pos (Set.mem_Ioi.mpr hr) (Set.mem_Ioi.mpr hs) heq)
    simp [logarithmicMean, hrs]
    rw [Real.log_div hs.ne' hr.ne']
    field_simp [sub_ne_zero.mpr hrs, hlog]
    ring

private lemma affine_pos {r s t : ℝ} (hr : 0 < r) (hs : 0 < s)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : 0 < (1 - t) * r + t * s := by
  have ht0 : 0 ≤ t := ht.1
  have hright : 0 ≤ t * s := mul_nonneg ht0 hs.le
  by_cases htEq : t = 1
  · subst t
    simpa using hs
  · have htlt : t < 1 := by
      by_contra hnot
      apply htEq
      exact le_antisymm ht.2 (le_of_not_gt hnot)
    have hleft : 0 < (1 - t) * r := mul_pos (by linarith) hr
    exact add_pos_of_pos_of_nonneg hleft hright

private lemma affine_inv_continuousOn {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    ContinuousOn (fun t : ℝ => ((1 - t) * r + t * s)⁻¹) (Set.Icc (0 : ℝ) 1) := by
  have hcont : Continuous fun t : ℝ => (1 - t) * r + t * s := by fun_prop
  apply hcont.continuousOn.inv₀
  intro t ht
  exact (affine_pos hr hs ht).ne'

private lemma affine_inv_intervalIntegrable {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    IntervalIntegrable (fun t : ℝ => ((1 - t) * r + t * s)⁻¹) volume 0 1 := by
  have hcont := affine_inv_continuousOn hr hs
  have hcont' : ContinuousOn (fun t : ℝ => ((1 - t) * r + t * s)⁻¹)
      (Set.uIcc (0 : ℝ) 1) := by simpa using hcont
  exact hcont'.intervalIntegrable

private lemma logMean_combo_integral {r s u v : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) :
    ∫ t in (0 : ℝ)..1,
        (1 / 3 : ℝ) * ((1 - t) * r + t * s)⁻¹ -
          (1 / 5 : ℝ) * ((1 - t) * u + t * v)⁻¹ =
      1 / (3 * logarithmicMean r s) - 1 / (5 * logarithmicMean u v) := by
  have hir := affine_inv_intervalIntegrable hr hs
  have hiu := affine_inv_intervalIntegrable hu hv
  rw [intervalIntegral.integral_sub (hir.const_mul (1 / 3 : ℝ))
    (hiu.const_mul (1 / 5 : ℝ))]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [← reciprocal_logarithmicMean_integral hr hs,
    ← reciprocal_logarithmicMean_integral hu hv]
  ring

private lemma kernel_mono_y {c x y y' t : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1) (hx : 0 < x) (hy : 0 < y) (hy' : 0 < y')
    (hyy : y ≤ y') (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (1 / 3 : ℝ) * ((1 - t) * (c * x) + t * y')⁻¹ -
        (1 / 5 : ℝ) * ((1 - t) * x + t * y')⁻¹ ≤
      (1 / 3 : ℝ) * ((1 - t) * (c * x) + t * y)⁻¹ -
        (1 / 5 : ℝ) * ((1 - t) * x + t * y)⁻¹ := by
  let A := (1 - t) * x
  let B := t * y
  let B' := t * y'
  let D := c * A + B
  let D' := c * A + B'
  let E := A + B
  let E' := A + B'
  have hA : 0 ≤ A := mul_nonneg (by linarith [ht.2]) hx.le
  have hB : 0 ≤ B := mul_nonneg ht.1 hy.le
  have hB' : 0 ≤ B' := mul_nonneg ht.1 hy'.le
  have hB_le : B ≤ B' := mul_le_mul_of_nonneg_left hyy ht.1
  have hD : 0 < D := by
    dsimp [D, A, B]
    calc
      0 < (1 - t) * (c * x) + t * y := affine_pos (mul_pos hc0 hx) hy ht
      _ = c * ((1 - t) * x) + t * y := by ring
  have hD' : 0 < D' := by
    dsimp [D', A, B']
    calc
      0 < (1 - t) * (c * x) + t * y' := affine_pos (mul_pos hc0 hx) hy' ht
      _ = c * ((1 - t) * x) + t * y' := by ring
  have hE : 0 < E := by
    dsimp [E, A, B]
    exact affine_pos hx hy ht
  have hE' : 0 < E' := by
    dsimp [E', A, B']
    exact affine_pos hx hy' ht
  have hD_le : D ≤ E := by
    dsimp [D, E]
    nlinarith [mul_nonneg hA (sub_nonneg.mpr hc1)]
  have hD'_le : D' ≤ E' := by
    dsimp [D', E']
    nlinarith [mul_nonneg hA (sub_nonneg.mpr hc1)]
  have hprod : D * D' ≤ E * E' := by
    exact mul_le_mul hD_le hD'_le (le_of_lt hD') (le_of_lt hE)
  have hcross : 3 * D * D' ≤ 5 * E * E' := by nlinarith
  have hformula :
      ((1 / 3 : ℝ) * D⁻¹ - (1 / 5 : ℝ) * E⁻¹) -
          ((1 / 3 : ℝ) * D'⁻¹ - (1 / 5 : ℝ) * E'⁻¹) =
        (B' - B) * ((1 / 3 : ℝ) * (D * D')⁻¹ -
          (1 / 5 : ℝ) * (E * E')⁻¹) := by
    field_simp [ne_of_gt hD, ne_of_gt hD', ne_of_gt hE, ne_of_gt hE']
    ring
  have hbracket :
      0 ≤ (1 / 3 : ℝ) * (D * D')⁻¹ - (1 / 5 : ℝ) * (E * E')⁻¹ := by
    have hDprod : 0 < D * D' := mul_pos hD hD'
    have hEprod : 0 < E * E' := mul_pos hE hE'
    have hcross' : 3 * (D * D') ≤ 5 * (E * E') := by nlinarith [hcross]
    rw [show (1 / 3 : ℝ) * (D * D')⁻¹ = (3 * (D * D'))⁻¹ by field_simp]
    rw [show (1 / 5 : ℝ) * (E * E')⁻¹ = (5 * (E * E'))⁻¹ by field_simp]
    exact sub_nonneg.mpr <| by
      simpa [one_div] using
        (one_div_le_one_div_of_le (by positivity : 0 < 3 * (D * D')) hcross')
  have hdelta : 0 ≤ B' - B := sub_nonneg.mpr hB_le
  have hfinal := mul_nonneg hdelta hbracket
  have : (1 / 3 : ℝ) * D'⁻¹ - (1 / 5 : ℝ) * E'⁻¹ ≤
      (1 / 3 : ℝ) * D⁻¹ - (1 / 5 : ℝ) * E⁻¹ := by linarith [hformula]
  change (1 / 3 : ℝ) * ((1 - t) * (c * x) + t * y')⁻¹ -
      (1 / 5 : ℝ) * ((1 - t) * x + t * y')⁻¹ ≤
    (1 / 3 : ℝ) * ((1 - t) * (c * x) + t * y)⁻¹ -
      (1 / 5 : ℝ) * ((1 - t) * x + t * y)⁻¹
  convert this using 1 <;> congr 1 <;> ring

theorem main : AKLT.Blueprint.Rec.LogCoefficientMonoYStatement := by
  intro c x y y' hcLower hcUpper hx hy hyy
  have hc0 : 0 < c := by linarith
  have hy' : 0 < y' := lt_of_lt_of_le hy hyy
  have hcy : 0 < c * x := mul_pos hc0 hx
  let f' : ℝ → ℝ := fun t =>
    (1 / 3 : ℝ) * ((1 - t) * (c * x) + t * y')⁻¹ -
      (1 / 5 : ℝ) * ((1 - t) * x + t * y')⁻¹
  let f : ℝ → ℝ := fun t =>
    (1 / 3 : ℝ) * ((1 - t) * (c * x) + t * y)⁻¹ -
      (1 / 5 : ℝ) * ((1 - t) * x + t * y)⁻¹
  have hf'cont : ContinuousOn f' (Set.Icc (0 : ℝ) 1) := by
    dsimp [f']
    exact (affine_inv_continuousOn hcy hy').const_mul _ |>.sub
      ((affine_inv_continuousOn hx hy').const_mul _)
  have hfcont : ContinuousOn f (Set.Icc (0 : ℝ) 1) := by
    dsimp [f]
    exact (affine_inv_continuousOn hcy hy).const_mul _ |>.sub
      ((affine_inv_continuousOn hx hy).const_mul _)
  have hf'cont' : ContinuousOn f' (Set.uIcc (0 : ℝ) 1) := by simpa using hf'cont
  have hfcont' : ContinuousOn f (Set.uIcc (0 : ℝ) 1) := by simpa using hfcont
  have hf'int : IntervalIntegrable f' volume 0 1 := hf'cont'.intervalIntegrable
  have hfint : IntervalIntegrable f volume 0 1 := hfcont'.intervalIntegrable
  have hmono : ∫ t in (0 : ℝ)..1, f' t ≤ ∫ t in (0 : ℝ)..1, f t := by
    apply intervalIntegral.integral_mono_on (by norm_num) hf'int hfint
    intro t ht
    exact kernel_mono_y hc0 hcUpper hx hy hy' hyy ht
  have hEq' := logMean_combo_integral hcy hy' hx hy'
  have hEq := logMean_combo_integral hcy hy hx hy
  calc
    _ = ∫ t in (0 : ℝ)..1, f' t := hEq'.symm
    _ ≤ ∫ t in (0 : ℝ)..1, f t := hmono
    _ = _ := hEq

end AKLT.W.REC025
