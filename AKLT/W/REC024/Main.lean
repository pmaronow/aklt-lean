import AKLT.Blueprint.Rec.NodesLogMean
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
open scoped BigOperators
open MeasureTheory
open AKLT.Defs

namespace AKLT.W.REC024

private theorem recipLogMean_integral (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    (logarithmicMean u v)⁻¹ = ∫ t in (0 : ℝ)..1, ((1 - t) * u + t * v)⁻¹ := by
  by_cases huv : u = v
  · subst v
    have heq : (fun t : ℝ => ((1 - t) * u + t * u)⁻¹) = fun _ => u⁻¹ := by
      funext t
      congr 1
      ring
    rw [heq]
    simp [logarithmicMean]
  · have hd : v - u ≠ 0 := sub_ne_zero.mpr (Ne.symm huv)
    have hchange :
        (∫ t in (0 : ℝ)..1, ((1 - t) * u + t * v)⁻¹) =
          (v - u)⁻¹ * ∫ z in u..v, z⁻¹ := by
      rw [show (fun t : ℝ => ((1 - t) * u + t * v)⁻¹) =
          (fun t => (u + (v - u) * t)⁻¹) by
            funext t
            congr 1
            ring]
      rw [intervalIntegral.integral_comp_add_mul (f := fun z : ℝ => z⁻¹) hd u]
      simp only [zero_mul, add_zero, mul_one]
      norm_num
    rw [hchange, integral_inv_of_pos hu hv]
    rw [logarithmicMean, if_neg huv]
    rw [Real.log_div hv.ne' hu.ne']
    have hlog : Real.log u - Real.log v ≠ 0 := by
      apply sub_ne_zero.mpr
      intro he
      exact huv (Real.log_injOn_pos (Set.mem_Ioi.mpr hu) (Set.mem_Ioi.mpr hv) he)
    field_simp [hlog, hd]
    <;> ring

end AKLT.W.REC024

namespace AKLT.W.REC024

theorem main : AKLT.Blueprint.Rec.LogCoefficientMonoXStatement := by
  intro c x x' y hc hc1 hx hxx hy
  have hcpos : 0 < c := by linarith
  have hcx : 0 < c * x := mul_pos hcpos hx
  have hcx' : 0 < c * x' := mul_pos hcpos (lt_of_lt_of_le hx hxx)
  have hLne (u v : ℝ) (hu : 0 < u) (hv : 0 < v) : logarithmicMean u v ≠ 0 := by
    by_cases huv : u = v
    · subst v
      simp [logarithmicMean, hu.ne']
    · have hlog : Real.log u - Real.log v ≠ 0 := by
        apply sub_ne_zero.mpr
        intro h
        exact huv (Real.log_injOn_pos (Set.mem_Ioi.mpr hu) (Set.mem_Ioi.mpr hv) h)
      simp [logarithmicMean, huv, sub_ne_zero.mpr huv, hlog]
  have hid (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
      1 / (3 * logarithmicMean u v) =
        ∫ t in (0 : ℝ)..1, 1 / (3 * ((1 - t) * u + t * v)) := by
    have hne := hLne u v hu hv
    calc
      1 / (3 * logarithmicMean u v) = (1 / 3) * (logarithmicMean u v)⁻¹ := by
        field_simp
      _ = (1 / 3) * ∫ t in (0 : ℝ)..1, ((1 - t) * u + t * v)⁻¹ := by
        rw [recipLogMean_integral u v hu hv]
      _ = ∫ t in (0 : ℝ)..1, (1 / 3) * ((1 - t) * u + t * v)⁻¹ := by
        rw [intervalIntegral.integral_const_mul]
      _ = ∫ t in (0 : ℝ)..1, 1 / (3 * ((1 - t) * u + t * v)) := by
        congr 1
        funext t
        simp [div_eq_mul_inv, mul_inv, mul_comm, mul_left_comm, mul_assoc]
  have hid5 (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
      1 / (5 * logarithmicMean u v) =
        ∫ t in (0 : ℝ)..1, 1 / (5 * ((1 - t) * u + t * v)) := by
    have hne := hLne u v hu hv
    calc
      1 / (5 * logarithmicMean u v) = (1 / 5) * (logarithmicMean u v)⁻¹ := by
        field_simp
      _ = (1 / 5) * ∫ t in (0 : ℝ)..1, ((1 - t) * u + t * v)⁻¹ := by
        rw [recipLogMean_integral u v hu hv]
      _ = ∫ t in (0 : ℝ)..1, (1 / 5) * ((1 - t) * u + t * v)⁻¹ := by
        rw [intervalIntegral.integral_const_mul]
      _ = ∫ t in (0 : ℝ)..1, 1 / (5 * ((1 - t) * u + t * v)) := by
        congr 1
        funext t
        simp [div_eq_mul_inv, mul_inv, mul_comm, mul_left_comm, mul_assoc]
  rw [hid (c * x') y hcx' hy, hid5 x' y (lt_of_lt_of_le hx hxx) hy,
    hid (c * x) y hcx hy, hid5 x y hx hy]
  have hmono : ∀ t : ℝ, t ∈ Set.Icc 0 1 →
      1 / (3 * ((1 - t) * (c * x') + t * y)) -
        1 / (5 * ((1 - t) * x' + t * y)) ≤
      1 / (3 * ((1 - t) * (c * x) + t * y)) -
        1 / (5 * ((1 - t) * x + t * y)) := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    let A := (1 - t) * x
    let Ap := (1 - t) * x'
    let B := t * y
    have hA : 0 ≤ A := mul_nonneg (by linarith) (le_of_lt hx)
    have hAp : 0 ≤ Ap := mul_nonneg (by linarith) (le_trans (le_of_lt hx) hxx)
    have hB : 0 ≤ B := mul_nonneg ht0 (le_of_lt hy)
    have hAAp : A ≤ Ap := by dsimp [A, Ap]; exact mul_le_mul_of_nonneg_left hxx (by linarith)
    have hq : 0 < A + B := by
      by_cases htEq : t = 1
      · simp [A, B, htEq, hy]
      · have htlt : t < 1 := lt_of_le_of_ne ht1 htEq
        have : 0 < (1 - t) * x := mul_pos (by linarith) hx
        dsimp [A, B]
        have hb : 0 ≤ t * y := mul_nonneg ht0 (le_of_lt hy)
        linarith
    have hqp : 0 < Ap + B := by
      have hle : A + B ≤ Ap + B := by nlinarith [hAAp]
      exact lt_of_lt_of_le hq hle
    have hp : 0 < c * A + B := by nlinarith [mul_pos hcpos (show 0 < A + B by linarith)]
    have hpp : 0 < c * Ap + B := by nlinarith [mul_pos hcpos (show 0 < Ap + B by linarith)]
    have h1c : 0 ≤ 1 - c := by linarith
    have hp_le : c * A + B ≤ A + B := by nlinarith [mul_nonneg h1c hA]
    have hpp_le : c * Ap + B ≤ Ap + B := by nlinarith [mul_nonneg h1c hAp]
    have hden :
        3 * ((c * Ap + B) * (c * A + B)) ≤
          5 * c * ((Ap + B) * (A + B)) := by
      have hprod := mul_le_mul hpp_le hp_le (le_of_lt hp) (le_of_lt hqp)
      have hfactor : 3 ≤ 5 * c := by linarith
      have hfactor' := mul_le_mul_of_nonneg_right hfactor
        (mul_nonneg (le_of_lt hqp) (le_of_lt hq))
      nlinarith
    have hcoeff :
        1 / (5 * (Ap + B) * (A + B)) ≤
          c / (3 * (c * Ap + B) * (c * A + B)) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      nlinarith [hden]
    have hdiff : 0 ≤ Ap - A := sub_nonneg.mpr hAAp
    have hcalc :
        (1 / (3 * (c * Ap + B)) - 1 / (5 * (Ap + B))) -
          (1 / (3 * (c * A + B)) - 1 / (5 * (A + B))) =
            (Ap - A) *
              (1 / (5 * (Ap + B) * (A + B)) -
                c / (3 * (c * Ap + B) * (c * A + B))) := by
      field_simp [ne_of_gt hp, ne_of_gt hpp, ne_of_gt hq, ne_of_gt hqp]
      <;> ring
    have hlocal :
        1 / (3 * (c * Ap + B)) - 1 / (5 * (Ap + B)) ≤
          1 / (3 * (c * A + B)) - 1 / (5 * (A + B)) := by
      apply sub_nonpos.mp
      rw [hcalc]
      exact mul_nonpos_of_nonneg_of_nonpos hdiff (sub_nonpos.mpr hcoeff)
    simpa [A, Ap, B, mul_assoc, mul_left_comm, mul_comm] using hlocal
  have hi1 : IntervalIntegrable
      (fun t : ℝ => 1 / (3 * ((1 - t) * (c * x') + t * y))) volume 0 1 := by
    apply intervalIntegral.intervalIntegrable_one_div
    · intro t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by simpa using ht
      have ht0 : 0 ≤ t := ht'.1
      have ht1 : t ≤ 1 := ht'.2
      have hpos : 0 < (1 - t) * (c * x') + t * y := by
        by_cases hzero : t = 1
        · subst t
          simpa using hy
        · have htlt : t < 1 := lt_of_le_of_ne ht1 hzero
          have hleft : 0 < (1 - t) * (c * x') := mul_pos (by linarith) hcx'
          have hright : 0 ≤ t * y := mul_nonneg ht0 (le_of_lt hy)
          linarith
      exact ne_of_gt (mul_pos (by norm_num) hpos)
    · fun_prop
  have hi2 : IntervalIntegrable
      (fun t : ℝ => 1 / (5 * ((1 - t) * x' + t * y))) volume 0 1 := by
    apply intervalIntegral.intervalIntegrable_one_div
    · intro t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by simpa using ht
      have ht0 : 0 ≤ t := ht'.1
      have ht1 : t ≤ 1 := ht'.2
      have hpos : 0 < (1 - t) * x' + t * y := by
        by_cases hzero : t = 1
        · subst t
          simpa using hy
        · have htlt : t < 1 := lt_of_le_of_ne ht1 hzero
          have hleft : 0 < (1 - t) * x' := mul_pos (by linarith) (lt_of_lt_of_le hx hxx)
          have hright : 0 ≤ t * y := mul_nonneg ht0 (le_of_lt hy)
          linarith
      exact ne_of_gt (mul_pos (by norm_num) hpos)
    · fun_prop
  have hi3 : IntervalIntegrable
      (fun t : ℝ => 1 / (3 * ((1 - t) * (c * x) + t * y))) volume 0 1 := by
    apply intervalIntegral.intervalIntegrable_one_div
    · intro t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by simpa using ht
      have ht0 : 0 ≤ t := ht'.1
      have ht1 : t ≤ 1 := ht'.2
      have hpos : 0 < (1 - t) * (c * x) + t * y := by
        by_cases hzero : t = 1
        · subst t
          simpa using hy
        · have htlt : t < 1 := lt_of_le_of_ne ht1 hzero
          have hleft : 0 < (1 - t) * (c * x) := mul_pos (by linarith) hcx
          have hright : 0 ≤ t * y := mul_nonneg ht0 (le_of_lt hy)
          linarith
      exact ne_of_gt (mul_pos (by norm_num) hpos)
    · fun_prop
  have hi4 : IntervalIntegrable
      (fun t : ℝ => 1 / (5 * ((1 - t) * x + t * y))) volume 0 1 := by
    apply intervalIntegral.intervalIntegrable_one_div
    · intro t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by simpa using ht
      have ht0 : 0 ≤ t := ht'.1
      have ht1 : t ≤ 1 := ht'.2
      have hpos : 0 < (1 - t) * x + t * y := by
        by_cases hzero : t = 1
        · subst t
          simpa using hy
        · have htlt : t < 1 := lt_of_le_of_ne ht1 hzero
          have hleft : 0 < (1 - t) * x := mul_pos (by linarith) hx
          have hright : 0 ≤ t * y := mul_nonneg ht0 (le_of_lt hy)
          linarith
      exact ne_of_gt (mul_pos (by norm_num) hpos)
    · fun_prop
  have hI := intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1)
    (f := fun t : ℝ => 1 / (3 * ((1 - t) * (c * x') + t * y)) -
      1 / (5 * ((1 - t) * x' + t * y)))
    (g := fun t : ℝ => 1 / (3 * ((1 - t) * (c * x) + t * y)) -
      1 / (5 * ((1 - t) * x + t * y))) (by norm_num)
    (hi1.sub hi2) (hi3.sub hi4) hmono
  simpa only [intervalIntegral.integral_sub hi1 hi2,
    intervalIntegral.integral_sub hi3 hi4] using hI

end AKLT.W.REC024
