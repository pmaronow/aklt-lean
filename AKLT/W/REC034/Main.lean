import AKLT.Blueprint.Rec.NodesLocal

noncomputable section

open AKLT.Defs
open MeasureTheory

namespace AKLT.W.REC034

private lemma affine_pos_on {x y t : ℝ} (hx : 0 < x) (hy : 0 < y)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : 0 < (1 - t) * x + t * y := by
  have hmin : 0 < min x y := lt_min hx hy
  have htx : 0 ≤ 1 - t := by linarith [ht.2]
  have hty : 0 ≤ t := ht.1
  have hmx : min x y ≤ x := min_le_left x y
  have hmy : min x y ≤ y := min_le_right x y
  have h1 := mul_nonneg htx (sub_nonneg.mpr hmx)
  have h2 := mul_nonneg hty (sub_nonneg.mpr hmy)
  nlinarith

private lemma logMean_inv_integral (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (logarithmicMean x y)⁻¹ =
      ∫ t in (0 : ℝ)..1, ((1 - t) * x + t * y)⁻¹ := by
  by_cases hxy : x = y
  · subst y
    have hfun : (fun t : ℝ => ((1 - t) * x + t * x)⁻¹) = fun _ => x⁻¹ := by
      funext t
      congr 1
      ring
    rw [hfun]
    simp [logarithmicMean, intervalIntegral.integral_const]
  · have hlog : Real.log x ≠ Real.log y := by
      intro h
      exact hxy (Real.log_injOn_pos (Set.mem_Ioi.mpr hx) (Set.mem_Ioi.mpr hy) h)
    have hc : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
    have hcomp :
        (∫ t in (0 : ℝ)..1, ((y - x) * t + x)⁻¹) =
          (y - x)⁻¹ * (Real.log y - Real.log x) := by
      calc
        (∫ t in (0 : ℝ)..1, ((y - x) * t + x)⁻¹) =
            (y - x)⁻¹ • (∫ z in x..y, z⁻¹) := by
              simpa using (intervalIntegral.integral_comp_mul_add
                (f := fun z : ℝ => z⁻¹) (a := (0 : ℝ)) (b := 1) hc x)
        _ = (y - x)⁻¹ * (Real.log y - Real.log x) := by
              rw [integral_inv_of_pos hx hy, Real.log_div hy.ne' hx.ne']
              simp [smul_eq_mul]
    have hform : ((x - y) / (Real.log x - Real.log y))⁻¹ =
        (y - x)⁻¹ * (Real.log y - Real.log x) := by
      field_simp [sub_ne_zero.mpr hxy, hlog]
      ring
    calc
      (logarithmicMean x y)⁻¹ = ((x - y) / (Real.log x - Real.log y))⁻¹ := by
        simp [logarithmicMean, hxy]
      _ = (y - x)⁻¹ * (Real.log y - Real.log x) := hform
      _ = ∫ t in (0 : ℝ)..1, ((y - x) * t + x)⁻¹ := hcomp.symm
      _ = ∫ t in (0 : ℝ)..1, ((1 - t) * x + t * y)⁻¹ := by
        apply intervalIntegral.integral_congr
        intro t ht
        ring

private lemma logMean_inv_mono (x x' y y' : ℝ) (hx : 0 < x) (hxx : x ≤ x')
    (hy : 0 < y) (hyy : y ≤ y') :
    (logarithmicMean x' y')⁻¹ ≤ (logarithmicMean x y)⁻¹ := by
  rw [logMean_inv_integral x' y' (lt_of_lt_of_le hx hxx) (lt_of_lt_of_le hy hyy),
    logMean_inv_integral x y hx hy]
  have hcont (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
      ContinuousOn (fun t : ℝ => ((1 - t) * u + t * v)⁻¹) (Set.Icc (0 : ℝ) 1) := by
    apply (show ContinuousOn (fun t : ℝ => (1 - t) * u + t * v) (Set.Icc (0 : ℝ) 1) from by fun_prop).inv₀
    intro t ht
    exact ne_of_gt (affine_pos_on hu hv ht)
  have hf : IntervalIntegrable (fun t : ℝ => ((1 - t) * x' + t * y')⁻¹) volume 0 1 :=
    (hcont x' y' (lt_of_lt_of_le hx hxx) (lt_of_lt_of_le hy hyy)).intervalIntegrable_of_Icc
      (μ := volume) (by norm_num)
  have hg : IntervalIntegrable (fun t : ℝ => ((1 - t) * x + t * y)⁻¹) volume 0 1 :=
    (hcont x y hx hy).intervalIntegrable_of_Icc (μ := volume) (by norm_num)
  apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hf hg
  intro t ht
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have hleft : 0 ≤ 1 - t := by linarith
  have hlin : (1 - t) * x + t * y ≤ (1 - t) * x' + t * y' := by
    have h1 := mul_nonneg hleft (sub_nonneg.mpr hxx)
    have h2 := mul_nonneg ht0 (sub_nonneg.mpr hyy)
    nlinarith
  have hpos := affine_pos_on hx hy ht
  have hpos' := affine_pos_on (lt_of_lt_of_le hx hxx) (lt_of_lt_of_le hy hyy) ht
  exact (inv_le_inv₀ hpos' hpos).2 hlin

theorem main : AKLT.Blueprint.Rec.BetaPrimeAnalyticStatement := by
  intro c It I₀ hc hIt hI₀
  have hmono := logMean_inv_mono c It 1 I₀ hc hIt one_pos hI₀
  change 1 / (3 * logarithmicMean It I₀) ≤
    (logarithmicMean c 1)⁻¹ / 3
  calc
    1 / (3 * logarithmicMean It I₀) = (logarithmicMean It I₀)⁻¹ / 3 := by
      simp [div_eq_mul_inv, mul_inv_rev, mul_comm]
    _ ≤ (logarithmicMean c 1)⁻¹ / 3 :=
      div_le_div_of_nonneg_right hmono (by norm_num : (0 : ℝ) ≤ 3)

end AKLT.W.REC034

#print axioms AKLT.W.REC034.main
