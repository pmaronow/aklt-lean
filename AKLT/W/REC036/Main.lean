module
public import AKLT.Blueprint.Rec.NodesLocal
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open AKLT.Defs
open scoped BigOperators

namespace AKLT.W.REC036

private def affineMean (x y t : ℝ) : ℝ := (1 - t) * x + t * y

private def alphaIntegrand (c x y t : ℝ) : ℝ :=
  (3 * affineMean (c * x) y t)⁻¹ - (5 * affineMean x y t)⁻¹

private theorem inv_logarithmicMean_integral {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (logarithmicMean x y)⁻¹ = ∫ t in (0 : ℝ)..1, ((1 - t) * x + t * y)⁻¹ := by
  by_cases hxy : x = y
  · subst y
    have hfun : (fun t : ℝ => ((1 - t) * x + t * x)⁻¹) = fun _ => x⁻¹ := by
      funext t
      congr 1
      ring
    simp [logarithmicMean, hfun]
  · have hd : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
    have hi := intervalIntegral.integral_comp_mul_add
      (a := (0 : ℝ)) (b := 1) (f := fun u : ℝ => u⁻¹) hd x
    rw [show (fun t : ℝ => ((1 - t) * x + t * y)⁻¹) =
        (fun t => ((y - x) * t + x)⁻¹) by
      funext t
      ring_nf]
    rw [hi]
    simp only [mul_zero, zero_add, mul_one, sub_add_cancel]
    rw [integral_inv_of_pos hx hy]
    simp only [smul_eq_mul]
    have hlog : Real.log (y / x) = Real.log y - Real.log x := Real.log_div hy.ne' hx.ne'
    rw [logarithmicMean]
    simp only [ite_eq_right hxy]
    rw [inv_div]
    rw [hlog]
    field_simp
    ring

private theorem affineMean_pos {x y t : ℝ} (hx : 0 < x) (hy : 0 < y)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 < affineMean x y t := by
  dsimp [affineMean]
  have h₁ : 0 ≤ (1 - t) * x := mul_nonneg (by linarith) hx.le
  have h₂ : 0 ≤ t * y := mul_nonneg ht0 hy.le
  nlinarith

private theorem affineInv_intervalIntegrable {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    IntervalIntegrable (fun t : ℝ => (affineMean x y t)⁻¹) MeasureTheory.volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  have hc : ContinuousOn (fun t : ℝ => affineMean x y t) (Set.uIcc 0 1) := by
    dsimp [affineMean]
    fun_prop
  apply hc.inv₀
  intro t ht
  have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by simpa using ht
  exact (affineMean_pos hx hy ht'.1 ht'.2).ne'

private theorem inv_logarithmicMean_mono {x x' y y' : ℝ}
    (hx : 0 < x) (hx' : 0 < x') (hy : 0 < y) (hy' : 0 < y')
    (hxx : x ≤ x') (hyy : y ≤ y') :
    (logarithmicMean x' y')⁻¹ ≤ (logarithmicMean x y)⁻¹ := by
  rw [inv_logarithmicMean_integral hx' hy', inv_logarithmicMean_integral hx hy]
  apply intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1) (by norm_num)
    (affineInv_intervalIntegrable hx' hy') (affineInv_intervalIntegrable hx hy)
  intro t ht
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have hlin : affineMean x y t ≤ affineMean x' y' t := by
    dsimp [affineMean]
    have h₁ : 0 ≤ (1 - t) * (x' - x) :=
      mul_nonneg (by linarith) (sub_nonneg.mpr hxx)
    have h₂ : 0 ≤ t * (y' - y) := mul_nonneg ht0 (sub_nonneg.mpr hyy)
    nlinarith
  have hpos₁ := affineMean_pos hx' hy' ht0 ht1
  have hpos₂ := affineMean_pos hx hy ht0 ht1
  exact (inv_le_inv₀ hpos₁ hpos₂).2 hlin

private theorem scaledAffineInv_intervalIntegrable {a x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    IntervalIntegrable (fun t : ℝ => (a * affineMean x y t)⁻¹) MeasureTheory.volume 0 1 := by
  have h := (affineInv_intervalIntegrable hx hy).smul (a⁻¹)
  have heq : (fun t : ℝ => (a * affineMean x y t)⁻¹) =
      fun t => a⁻¹ * (affineMean x y t)⁻¹ := by
    funext t
    simp [mul_comm]
  rw [heq]
  convert h using 1

private theorem scaledInvMean_integral {a x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    1 / (a * logarithmicMean x y) =
      ∫ t in (0 : ℝ)..1, (a * affineMean x y t)⁻¹ := by
  have h := inv_logarithmicMean_integral hx hy
  calc
    1 / (a * logarithmicMean x y) = a⁻¹ * (logarithmicMean x y)⁻¹ := by
      simp [div_eq_mul_inv, mul_comm]
    _ = a⁻¹ * ∫ t in (0 : ℝ)..1, (affineMean x y t)⁻¹ := by
      simpa [affineMean] using congrArg (fun z => a⁻¹ * z) h
    _ = ∫ t in (0 : ℝ)..1, a⁻¹ * (affineMean x y t)⁻¹ := by
      rw [intervalIntegral.integral_const_mul]
    _ = ∫ t in (0 : ℝ)..1, (a * affineMean x y t)⁻¹ := by
      congr 1
      funext t
      simp [mul_comm]

private theorem alphaKernel_integral {c x y : ℝ}
    (hc : 0 < c) (hx : 0 < x) (hy : 0 < y) :
    1 / (3 * logarithmicMean (c * x) y) - 1 / (5 * logarithmicMean x y) =
      ∫ t in (0 : ℝ)..1, alphaIntegrand c x y t := by
  have hc' : 0 < c * x := mul_pos hc hx
  have hfirst := scaledInvMean_integral (a := 3) (x := c * x) (y := y) hc' hy
  have hsecond := scaledInvMean_integral (a := 5) (x := x) (y := y) hx hy
  have hf : IntervalIntegrable (fun t : ℝ => (3 * affineMean (c * x) y t)⁻¹)
      MeasureTheory.volume 0 1 := scaledAffineInv_intervalIntegrable hc' hy
  have hg : IntervalIntegrable (fun t : ℝ => (5 * affineMean x y t)⁻¹)
      MeasureTheory.volume 0 1 := scaledAffineInv_intervalIntegrable hx hy
  rw [hfirst, hsecond, ← intervalIntegral.integral_sub hf hg]
  rfl

private theorem alphaIntegrand_intervalIntegrable {c x y : ℝ}
    (hc : 0 < c) (hx : 0 < x) (hy : 0 < y) :
    IntervalIntegrable (fun t : ℝ => alphaIntegrand c x y t) MeasureTheory.volume 0 1 := by
  have h₁ := scaledAffineInv_intervalIntegrable (a := 3) (mul_pos hc hx) hy
  have h₂ := scaledAffineInv_intervalIntegrable (a := 5) hx hy
  change IntervalIntegrable
    (fun t : ℝ => (3 * affineMean (c * x) y t)⁻¹ - (5 * affineMean x y t)⁻¹)
    MeasureTheory.volume 0 1
  exact h₁.sub h₂

private theorem alphaIntegrand_mono_x {c x x' y t : ℝ}
    (hc₀ : 3 / 5 ≤ c) (hc₁ : c ≤ 1) (hx : 0 < x) (hx' : 0 < x')
    (hy : 0 < y) (hxx : x ≤ x') (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    alphaIntegrand c x' y t ≤ alphaIntegrand c x y t := by
  have hc : 0 < c := by linarith
  let d := affineMean (c * x) y t
  let dp := affineMean (c * x') y t
  let e := affineMean x y t
  let ep := affineMean x' y t
  have hd : 0 < d := affineMean_pos (mul_pos hc hx) hy ht0 ht1
  have hdp : 0 < dp := affineMean_pos (mul_pos hc hx') hy ht0 ht1
  have he : 0 < e := affineMean_pos hx hy ht0 ht1
  have hep : 0 < ep := affineMean_pos hx' hy ht0 ht1
  have hde : d ≤ e := by
    dsimp [d, e, affineMean]
    have hnonneg : 0 ≤ (1 - t) * ((1 - c) * x) :=
      mul_nonneg (by linarith) (mul_nonneg (by linarith) hx.le)
    nlinarith
  have hdpe : dp ≤ ep := by
    dsimp [dp, ep, affineMean]
    have hnonneg : 0 ≤ (1 - t) * ((1 - c) * x') :=
      mul_nonneg (by linarith) (mul_nonneg (by linarith) hx'.le)
    nlinarith
  have hprod : dp * d ≤ ep * e := by
    calc
      dp * d ≤ ep * d := mul_le_mul_of_nonneg_right hdpe hd.le
      _ ≤ ep * e := mul_le_mul_of_nonneg_left hde hep.le
  have hcoef : 3 ≤ 5 * c := by linarith
  have hcomp : 3 * dp * d ≤ 5 * c * ep * e := by
    calc
      3 * dp * d ≤ 3 * (ep * e) := by nlinarith [hprod]
      _ ≤ 5 * c * (ep * e) := by
        exact mul_le_mul_of_nonneg_right hcoef (mul_nonneg hep.le he.le)
      _ = 5 * c * ep * e := by ring
  have hfrac : 1 / (5 * ep * e) ≤ c / (3 * dp * d) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [hcomp]
  have hdelta : 0 ≤ (1 - t) * (x' - x) :=
    mul_nonneg (by linarith) (sub_nonneg.mpr hxx)
  have hfactor : alphaIntegrand c x' y t - alphaIntegrand c x y t =
      (1 - t) * (x' - x) * (1 / (5 * ep * e) - c / (3 * dp * d)) := by
    have hE : ep - e = (1 - t) * (x' - x) := by
      dsimp [ep, e, affineMean]
      ring
    have hD : dp - d = c * ((1 - t) * (x' - x)) := by
      dsimp [dp, d, affineMean]
      ring
    have hD' : d - dp = -c * ((1 - t) * (x' - x)) := by linarith
    change (3 * dp)⁻¹ - (5 * ep)⁻¹ - ((3 * d)⁻¹ - (5 * e)⁻¹) = _
    field_simp [ne_of_gt hd, ne_of_gt hdp, ne_of_gt he, ne_of_gt hep]
    nlinarith [congrArg (fun z => 3 * dp * d * z) hE,
      congrArg (fun z => 5 * ep * e * z) hD']
  have hdiff : alphaIntegrand c x' y t - alphaIntegrand c x y t ≤ 0 := by
    rw [hfactor]
    exact mul_nonpos_of_nonneg_of_nonpos hdelta (sub_nonpos.mpr hfrac)
  linarith

private theorem alphaIntegrand_mono_y {c x y y' t : ℝ}
    (hc₀ : 3 / 5 ≤ c) (hc₁ : c ≤ 1) (hx : 0 < x) (hy : 0 < y)
    (hy' : 0 < y') (hyy : y ≤ y') (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    alphaIntegrand c x y' t ≤ alphaIntegrand c x y t := by
  have hc : 0 < c := by linarith
  let d := affineMean (c * x) y t
  let dp := affineMean (c * x) y' t
  let e := affineMean x y t
  let ep := affineMean x y' t
  have hd : 0 < d := affineMean_pos (mul_pos hc hx) hy ht0 ht1
  have hdp : 0 < dp := affineMean_pos (mul_pos hc hx) hy' ht0 ht1
  have he : 0 < e := affineMean_pos hx hy ht0 ht1
  have hep : 0 < ep := affineMean_pos hx hy' ht0 ht1
  have hde : d ≤ e := by
    dsimp [d, e, affineMean]
    have hnonneg : 0 ≤ (1 - t) * ((1 - c) * x) :=
      mul_nonneg (by linarith) (mul_nonneg (by linarith) hx.le)
    nlinarith
  have hdpe : dp ≤ ep := by
    dsimp [dp, ep, affineMean]
    have hnonneg : 0 ≤ (1 - t) * ((1 - c) * x) :=
      mul_nonneg (by linarith) (mul_nonneg (by linarith) hx.le)
    nlinarith
  have hprod : dp * d ≤ ep * e := by
    calc
      dp * d ≤ ep * d := mul_le_mul_of_nonneg_right hdpe hd.le
      _ ≤ ep * e := mul_le_mul_of_nonneg_left hde hep.le
  have hcomp : 3 * dp * d ≤ 5 * ep * e := by nlinarith [hprod]
  have hfrac : 1 / (5 * ep * e) ≤ 1 / (3 * dp * d) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [hcomp]
  have hdelta : 0 ≤ t * (y' - y) :=
    mul_nonneg ht0 (sub_nonneg.mpr hyy)
  have hfactor : alphaIntegrand c x y' t - alphaIntegrand c x y t =
      t * (y' - y) * (1 / (5 * ep * e) - 1 / (3 * dp * d)) := by
    have hE : ep - e = t * (y' - y) := by
      dsimp [ep, e, affineMean]
      ring
    have hD : dp - d = t * (y' - y) := by
      dsimp [dp, d, affineMean]
      ring
    have hD' : d - dp = -t * (y' - y) := by linarith
    change (3 * dp)⁻¹ - (5 * ep)⁻¹ - ((3 * d)⁻¹ - (5 * e)⁻¹) = _
    field_simp [ne_of_gt hd, ne_of_gt hdp, ne_of_gt he, ne_of_gt hep]
    nlinarith [congrArg (fun z => 3 * dp * d * z) hE,
      congrArg (fun z => 5 * ep * e * z) hD']
  have hdiff : alphaIntegrand c x y' t - alphaIntegrand c x y t ≤ 0 := by
    rw [hfactor]
    exact mul_nonpos_of_nonneg_of_nonpos hdelta (sub_nonpos.mpr hfrac)
  linarith

private theorem alphaKernel_mono_x {c x x' y : ℝ}
    (hc₀ : 3 / 5 ≤ c) (hc₁ : c ≤ 1) (hx : 0 < x) (hx' : 0 < x')
    (hy : 0 < y) (hxx : x ≤ x') :
    1 / (3 * logarithmicMean (c * x') y) - 1 / (5 * logarithmicMean x' y) ≤
      1 / (3 * logarithmicMean (c * x) y) - 1 / (5 * logarithmicMean x y) := by
  have hc : 0 < c := by linarith
  rw [alphaKernel_integral hc hx' hy, alphaKernel_integral hc hx hy]
  apply intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1) (by norm_num)
    (alphaIntegrand_intervalIntegrable hc hx' hy) (alphaIntegrand_intervalIntegrable hc hx hy)
  intro t ht
  exact alphaIntegrand_mono_x hc₀ hc₁ hx hx' hy hxx ht.1 ht.2

private theorem alphaKernel_mono_y {c x y y' : ℝ}
    (hc₀ : 3 / 5 ≤ c) (hc₁ : c ≤ 1) (hx : 0 < x) (hy : 0 < y)
    (hy' : 0 < y') (hyy : y ≤ y') :
    1 / (3 * logarithmicMean (c * x) y') - 1 / (5 * logarithmicMean x y') ≤
      1 / (3 * logarithmicMean (c * x) y) - 1 / (5 * logarithmicMean x y) := by
  have hc : 0 < c := by linarith
  rw [alphaKernel_integral hc hx hy', alphaKernel_integral hc hx hy]
  apply intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1) (by norm_num)
    (alphaIntegrand_intervalIntegrable hc hx hy') (alphaIntegrand_intervalIntegrable hc hx hy)
  intro t ht
  exact alphaIntegrand_mono_y hc₀ hc₁ hx hy hy' hyy ht.1 ht.2

theorem main : AKLT.Blueprint.Rec.AlphaAnalyticStatement := by
  intro c It I₀ Jt J₀ hc₀ hc₁ hIt hI₀ hJt hJ₀
  have hc : 0 < c := by linarith
  have hk : 0 < (116 / 125 : ℝ) := by norm_num
  have hJtpos : 0 < Jt := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 116 / 125) hJt
  have hJ₀pos : 0 < J₀ := lt_of_lt_of_le zero_lt_one hJ₀
  have hcJtpos : 0 < c * Jt := mul_pos hc hJtpos
  have hItpos : 0 < It := lt_of_lt_of_le hcJtpos hIt
  have hI₀pos : 0 < I₀ := lt_of_lt_of_le hJ₀pos hI₀
  have hInv := inv_logarithmicMean_mono hcJtpos hItpos hJ₀pos hI₀pos hIt hI₀
  have hscale (z : ℝ) : 1 / (3 * z) = z⁻¹ / 3 := by
    simp [div_eq_mul_inv, mul_comm]
  have hscale5 (z : ℝ) : 1 / (5 * z) = z⁻¹ / 5 := by
    simp [div_eq_mul_inv, mul_comm]
  have hBeta : 1 / (3 * logarithmicMean It I₀) ≤
      1 / (3 * logarithmicMean (c * Jt) J₀) := by
    rw [hscale, hscale]
    exact div_le_div_of_nonneg_right hInv (by norm_num)
  have hX := alphaKernel_mono_x hc₀ hc₁ hk hJtpos hJ₀pos hJt
  have hY := alphaKernel_mono_y hc₀ hc₁ hk (by norm_num) hJ₀pos hJ₀
  have hKernel :
      1 / (3 * logarithmicMean (c * Jt) J₀) - 1 / (5 * logarithmicMean Jt J₀) ≤
        1 / (3 * logarithmicMean (c * (116 / 125)) 1) -
          1 / (5 * logarithmicMean (116 / 125) 1) := le_trans hX hY
  calc
    1 / (3 * logarithmicMean It I₀) - 1 / (5 * logarithmicMean Jt J₀) ≤
        1 / (3 * logarithmicMean (c * Jt) J₀) -
          1 / (5 * logarithmicMean Jt J₀) := sub_le_sub_right hBeta _
    _ ≤ 1 / (3 * logarithmicMean (c * (116 / 125)) 1) -
          1 / (5 * logarithmicMean (116 / 125) 1) := hKernel
    _ = reciprocalLogMean ((116 / 125) * c) / 3 - reciprocalLogMean (116 / 125) / 5 := by
      rw [hscale, hscale5]
      simp [reciprocalLogMean, mul_comm]

end AKLT.W.REC036
