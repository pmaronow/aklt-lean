import AKLT.Blueprint.Rec.NodesLogMean

noncomputable section

open scoped BigOperators
open AKLT.Defs
open intervalIntegral

namespace AKLT.W.REC023

private lemma affine_pos {x y t : ℝ} (hx : 0 < x) (hy : 0 < y)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 < (1 - t) * x + t * y := by
  let m := min x y
  have hm : 0 < m := lt_min hx hy
  have h1 : 0 ≤ (1 - t) * (x - m) :=
    mul_nonneg (by linarith) (sub_nonneg.mpr (min_le_left x y))
  have h2 : 0 ≤ t * (y - m) :=
    mul_nonneg ht0 (sub_nonneg.mpr (min_le_right x y))
  have hsum : (1 - t) * (x - m) + t * (y - m) + m =
      (1 - t) * x + t * y := by ring
  rw [← hsum]
  linarith

private lemma reciprocal_affine_integral {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxy : x ≠ y) :
    (∫ t in (0 : ℝ)..1, ((1 - t) * x + t * y)⁻¹) =
      (Real.log y - Real.log x) / (y - x) := by
  let q : ℝ → ℝ := fun t => (1 - t) * x + t * y
  let F : ℝ → ℝ := fun t => (y - x)⁻¹ * Real.log (q t)
  have hqpos : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < q t := by
    intro t ht
    exact affine_pos hx hy ht.1 ht.2
  have hqcont : Continuous q := by
    dsimp [q]
    fun_prop
  have hqcontIcc : ContinuousOn q (Set.Icc (0 : ℝ) 1) := hqcont.continuousOn
  have hqne : ∀ t ∈ Set.Icc (0 : ℝ) 1, q t ≠ 0 :=
    fun t ht => (hqpos t ht).ne'
  have hFcont : ContinuousOn F (Set.Icc (0 : ℝ) 1) := by
    dsimp [F]
    exact (Real.continuousOn_log.comp hqcontIcc hqne).const_mul _
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt F (q t)⁻¹ t := by
    intro t ht
    have hqderiv : HasDerivAt q (y - x) t := by
      convert (hasDerivAt_const t x).add ((hasDerivAt_id t).const_mul (y - x)) using 1
      · funext z
        dsimp [q]
        ring
      · ring
    have hlog := hqderiv.log (hqpos t ⟨le_of_lt ht.1, le_of_lt ht.2⟩).ne'
    change HasDerivAt (fun z => (y - x)⁻¹ * Real.log (q z)) (q t)⁻¹ t
    convert hlog.const_mul (y - x)⁻¹ using 1 <;>
      field_simp [sub_ne_zero.mpr hxy]
  have hintegrable : IntervalIntegrable (fun t => (q t)⁻¹) MeasureTheory.volume 0 1 :=
    (hqcontIcc.inv₀ hqne).intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (0 : ℝ) ≤ 1) hFcont hderiv hintegrable
  rw [hFTC]
  dsimp [F]
  field_simp [sub_ne_zero.mpr hxy]
  simp [q]

theorem main : AKLT.Blueprint.Rec.ReciprocalIntegralStatement := by
  intro x y hx hy
  by_cases hxy : x = y
  · subst y
    have hfun : (fun t : ℝ => ((1 - t) * x + t * x)⁻¹) = fun _ => x⁻¹ := by
      funext t
      congr 1
      ring
    simp [AKLT.Defs.logarithmicMean, hfun]
  · have hlog : Real.log x ≠ Real.log y := by
      intro h
      rcases lt_or_gt_of_ne hxy with hlt | hgt
      · exact (ne_of_lt (Real.log_lt_log hx hlt)) h
      · exact (ne_of_gt (Real.log_lt_log hy hgt)) h
    have hInt := reciprocal_affine_integral hx hy hxy
    simp only [AKLT.Defs.logarithmicMean, if_neg hxy]
    rw [hInt]
    field_simp [sub_ne_zero.mpr hxy, sub_ne_zero.mpr hlog]
    <;> ring

#print axioms AKLT.W.REC023.main

end AKLT.W.REC023
