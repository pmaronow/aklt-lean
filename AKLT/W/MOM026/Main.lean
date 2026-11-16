import AKLT.Blueprint.Mom.NodesMean

noncomputable section
open scoped BigOperators
open AKLT.Defs
open AKLT.Blueprint.Mom

namespace AKLT.W.MOM026

private lemma goldenRatio_sq : goldenRatio ^ 2 = goldenRatio + 1 := by
  unfold goldenRatio
  have hs : Real.sqrt 5 ^ 2 = (5 : ℝ) := Real.sq_sqrt (by norm_num)
  nlinarith

private lemma icoRadius_sq : icoRadius ^ 2 = goldenRatio + 2 := by
  unfold icoRadius
  have hp : 0 ≤ goldenRatio + 2 := by
    unfold goldenRatio
    positivity
  exact Real.sq_sqrt hp

private lemma icoRadius_gt_one : 1 < icoRadius := by
  have hphi : 0 < goldenRatio := by
    unfold goldenRatio
    positivity
  have hr0 : 0 ≤ icoRadius := Real.sqrt_nonneg _
  have hr2 : (1 : ℝ) ^ 2 < icoRadius ^ 2 := by
    rw [icoRadius_sq]
    nlinarith
  exact (sq_lt_sq₀ (by norm_num) hr0).1 hr2

private lemma ico_unit (j : IcoLetter) : normSq (icoVector j) = 1 := by
  have hr : 0 < icoRadius := lt_trans (by norm_num) icoRadius_gt_one
  rcases j with ⟨a, b, c⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [normSq, dot, icoVector, signValue, Fin.sum_univ_three] <;>
    field_simp [ne_of_gt hr] <;>
    rw [icoRadius_sq, goldenRatio_sq] <;> ring

private lemma normSq_add (u v : Vec3) :
    normSq (u + v) = normSq u + 2 * dot u v + normSq v := by
  unfold normSq dot
  calc
    (∑ i, (u i + v i) * (u i + v i)) =
        ∑ i, (u i * u i + 2 * (u i * v i) + v i * v i) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = (∑ i, u i * u i) + 2 * (∑ i, u i * v i) + (∑ i, v i * v i) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]

private lemma dot_unit_lower (u v : Vec3) (hu : normSq u = 1) (hv : normSq v = 1) :
    -1 ≤ dot u v := by
  have h : 0 ≤ normSq (u + v) := by
    unfold normSq dot
    exact Finset.sum_nonneg (fun i hi => mul_self_nonneg ((u + v) i))
  rw [normSq_add, hu, hv] at h
  linarith

private lemma meanPath_den_pos (t : ℝ) :
    0 < siteFunctional .U (localProduct (meanPath t)) := by
  rw [siteLawDecomposition.1]
  unfold moment
  have hnonneg : ∀ j : IcoLetter,
      0 ≤ (1 / 12 : ℝ) * localProduct (meanPath t) (icoVector j) := by
    intro j
    have hfac : ∀ k : Fin 3, 0 ≤ 1 + dot (icoVector j) (meanPath t k) := by
      intro k
      have hdot := dot_unit_lower (icoVector j) (meanPath t k) (ico_unit j)
        (meanPathUnit t k)
      linarith
    unfold localProduct
    apply mul_nonneg
    · norm_num
    · exact Finset.prod_nonneg (fun k hk => hfac k)
  have hchosen : 0 < (1 / 12 : ℝ) * localProduct (meanPath t)
      (icoVector (0, 0, 0)) := by
    have hr : 1 < icoRadius := icoRadius_gt_one
    have hsin : |Real.sin t| ≤ 1 := Real.abs_sin_le_one t
    have hrpos : 0 < icoRadius := lt_trans (by norm_num) hr
    have hratio : |Real.sin t / icoRadius| < 1 := by
      rw [abs_div, abs_of_pos hrpos]
      exact (div_lt_one hrpos).2 (lt_of_le_of_lt hsin hr)
    have hsq : (Real.sin t / icoRadius) ^ 2 < 1 := by
      have habs : |Real.sin t / icoRadius| ^ 2 < 1 := by
        have habs0 : 0 ≤ |Real.sin t / icoRadius| := abs_nonneg _
        have hf : 0 < (1 - |Real.sin t / icoRadius|) *
            (1 + |Real.sin t / icoRadius|) :=
          mul_pos (by linarith) (by positivity)
        nlinarith
      simpa [sq_abs] using habs
    have hprod : localProduct (meanPath t) (icoVector (0, 0, 0)) =
        1 - (Real.sin t / icoRadius) ^ 2 := by
      simp [localProduct, meanPath, icoVector, signValue, dot, Fin.sum_univ_three,
        Fin.prod_univ_succ]
      <;> ring
    rw [hprod]
    positivity
  have hsum : 0 < ∑ j : IcoLetter,
      (1 / 12 : ℝ) * localProduct (meanPath t) (icoVector j) := by
    have hle := Finset.single_le_sum (fun j hj => hnonneg j)
      (show (0, 0, 0) ∈ (Finset.univ : Finset IcoLetter) by simp)
    have hterm : (1 / 12 : ℝ) * localProduct (meanPath t) (icoVector (0, 0, 0)) ≤
        ∑ j : IcoLetter, (1 / 12 : ℝ) * localProduct (meanPath t) (icoVector j) := by
      simpa using hle
    exact lt_of_lt_of_le hchosen hterm
  change 0 < (1 / 12 : ℝ) * ∑ j : IcoLetter,
    localProduct (meanPath t) (icoVector j)
  rw [Finset.mul_sum]
  exact hsum

theorem main : AKLT.Blueprint.Mom.MeanPathContinuityStatement := by
  unfold AKLT.Blueprint.Mom.MeanPathContinuityStatement
  let D : ℝ → ℝ := fun t => siteFunctional .U (localProduct (meanPath t))
  have hDcont : Continuous D := by
    dsimp [D, siteFunctional, localProduct, dot, meanPath]
    fun_prop
  have hNcont : ∀ i : Fin 3,
      Continuous (fun t => siteFunctional .U (fun n => n i * localProduct (meanPath t) n)) := by
    intro i
    dsimp [siteFunctional, localProduct, dot, meanPath]
    fun_prop
  have hmean : ContinuousOn (fun t => localMean .U (meanPath t)) (Set.Icc 0 meanPathEnd) := by
    apply continuousOn_pi.mpr
    intro i
    have hi : ContinuousOn
        (fun t => siteFunctional .U (fun n => n i * localProduct (meanPath t) n))
        (Set.Icc 0 meanPathEnd) := (hNcont i).continuousOn
    have hdi : ContinuousOn D (Set.Icc 0 meanPathEnd) := hDcont.continuousOn
    have hpos : ∀ t ∈ Set.Icc 0 meanPathEnd, D t ≠ 0 := by
      intro t ht
      exact ne_of_gt (meanPath_den_pos t)
    change ContinuousOn (fun t =>
      siteFunctional .U (fun n => n i * localProduct (meanPath t) n) /
        siteFunctional .U (localProduct (meanPath t))) (Set.Icc 0 meanPathEnd)
    exact hi.div hdi hpos
  change ContinuousOn (fun t => normSq (localMean .U (meanPath t))) _
  dsimp [normSq, dot]
  apply continuousOn_finsetSum
  intro i hi
  have hcoord := (continuousOn_pi.mp hmean i)
  exact hcoord.mul hcoord

end AKLT.W.MOM026
