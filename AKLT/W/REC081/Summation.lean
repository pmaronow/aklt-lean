module
public import AKLT.W.REC081.Geometry
public import AKLT.W.REC081.Positivity

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC081

theorem exceptionFactor_pos : 0 < exceptionFactor := by
  unfold exceptionFactor
  positivity

theorem onePointConstant_nonneg (CV q : ℝ) (h : OpenTrailBound CV q) :
    0 ≤ onePointConstant CV q := by
  unfold onePointConstant
  exact div_nonneg (mul_nonneg exceptionFactor_pos.le (by linarith [h.1]))
    (sub_pos.mpr h.2.2.1).le

theorem trailWeight_nonneg {n : ℕ} (u : Plane) (incoming : Compass)
    (w : DirectionWord n) : 0 ≤ trailWeight u incoming w := by
  unfold trailWeight
  apply Finset.prod_nonneg
  intro i _
  split
  · norm_num
  · cases wordStraight incoming w i <;> norm_num [passageFactor, localThreshold]

/-- H2 bounds the finite sum of the pointwise common majorants, with the
original protected distance determining the start of the geometric tail. -/
theorem onePointSum_le_of_pointwise {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (u : Plane) (incoming : Compass) (CV q : ℝ)
    (hOpen : OpenTrailBound CV q) (habs : ¬ D.Present (u - incoming.step) u)
    (hpoint : ∀ n : ℕ, ∀ w : DirectionWord n,
      StoppedNetworkTrail D u (protectedSites G) w →
      (traceCoefficient D (wordVertices u w) : ℝ) *
        max (traceRatio D τ true (wordVertices u w)) (traceRatio D τ false (wordVertices u w)) ≤
          exceptionFactor * (trailWeight u incoming w : ℝ)) :
    onePointSum D τ u ≤ onePointConstant CV q * q ^ (protectedDistance G u) := by
  classical
  let δ := protectedDistance G u
  have hCV : 0 ≤ CV := by linarith [hOpen.1]
  have hq : 0 ≤ q := hOpen.2.1.le
  have hlen : ∀ n : ℕ,
      (∑ w ∈ stoppedNetworkTrails D u (protectedSites G) n,
        (traceCoefficient D (wordVertices u w) : ℝ) *
          max (traceRatio D τ true (wordVertices u w)) (traceRatio D τ false (wordVertices u w))) ≤
        if δ ≤ n then (exceptionFactor * CV) * q^n else 0 := by
    intro n
    by_cases hn : δ ≤ n
    · rw [ite_eq_left hn]
      calc
        _ ≤ ∑ w : DirectionWord n,
            if IsTrail u incoming w then exceptionFactor * (trailWeight u incoming w : ℝ) else 0 := by
          unfold stoppedNetworkTrails
          rw [Finset.sum_filter]
          apply Finset.sum_le_sum
          intro w _
          by_cases hw : StoppedNetworkTrail D u (protectedSites G) w
          · simp only [ite_eq_left hw, ite_eq_left (stopped_isTrail D u incoming _ w habs hw)]
            exact hpoint n w hw
          · rw [ite_eq_right hw]
            split
            · exact mul_nonneg exceptionFactor_pos.le (by exact_mod_cast trailWeight_nonneg u incoming w)
            · exact le_rfl
        _ = exceptionFactor * ∑ w : DirectionWord n,
            if IsTrail u incoming w then (trailWeight u incoming w : ℝ) else 0 := by
          simp only [Finset.mul_sum, mul_ite, mul_zero]
        _ ≤ exceptionFactor * (CV * q^n) :=
          mul_le_mul_of_nonneg_left (hOpen.2.2.2 n u incoming) exceptionFactor_pos.le
        _ = _ := by ring
    · rw [ite_eq_right hn]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro w hw
      have hstop : StoppedNetworkTrail D u (protectedSites G) w := (Finset.mem_filter.mp hw).2
      exact (hn (stopped_length_ge_distance D u w hstop)).elim
  have hfilter : (Finset.range (D.bonds.card + 1)).filter (fun n => δ ≤ n) =
      Finset.Ico δ (D.bonds.card + 1) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  calc
    onePointSum D τ u ≤ ∑ n ∈ Finset.range (D.bonds.card + 1),
        if δ ≤ n then (exceptionFactor * CV) * q^n else 0 :=
      by simpa only [onePointSum, stoppedSum] using
        (Finset.sum_le_sum (s := Finset.range (D.bonds.card + 1)) (fun n _ => hlen n))
    _ = (exceptionFactor * CV) * ∑ n ∈ Finset.Ico δ (D.bonds.card + 1), q^n := by
      rw [← Finset.sum_filter, hfilter, Finset.mul_sum]
    _ ≤ (exceptionFactor * CV) * (q^δ / (1 - q)) :=
      mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hq hOpen.2.2.1)
        (mul_nonneg exceptionFactor_pos.le hCV)
    _ = onePointConstant CV q * q ^ (protectedDistance G u) := by
      unfold onePointConstant δ
      ring

theorem weighted_response_bound (a r s x y K : ℝ) (ha : 0 ≤ a) (hr : 0 ≤ r)
    (hs : 0 ≤ s) (hK : 0 ≤ K) (hx : |x| ≤ K) (hy : |y| ≤ K) :
    |a * (r * x - s * y)| ≤ (2 * K) * (a * max r s) := by
  have hrx : |r * x| ≤ max r s * K := by
    rw [abs_mul, abs_of_nonneg hr]
    exact (mul_le_mul_of_nonneg_left hx hr).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hK)
  have hsy : |s * y| ≤ max r s * K := by
    rw [abs_mul, abs_of_nonneg hs]
    exact (mul_le_mul_of_nonneg_left hy hs).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hK)
  calc
    _ = a * |r * x - s * y| := by rw [abs_mul, abs_of_nonneg ha]
    _ ≤ a * (max r s * K + max r s * K) :=
      mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add hrx hsy)) ha
    _ = _ := by ring

theorem stopped_boundary_trail {G : Finset Plane} {n : ℕ} (D : Network G)
    (u v : Plane) (w : DirectionWord n)
    (hw : StoppedNetworkTrail D u (insert v (protectedSites G)) w)
    (he : wordVertex u w n ≠ v) : StoppedNetworkTrail D u (protectedSites G) w := by
  refine ⟨hw.1, hw.2.1, ?_, ?_⟩
  · intro j hj
    exact ⟨(hw.2.2.1 j hj).2, (hw.2.2.1 j hj).2⟩
  · exact (Finset.mem_insert.mp hw.2.2.2).resolve_left he

/-- Remove the zero target summands and enlarge to every first hit of original S.
The maximum stays inside the first-trail sum throughout. -/
theorem secondTerm_le_onePointSum (p : PairData) (K : ℝ) (hK : 0 ≤ K)
    (hterminal : ∀ n : ℕ, ∀ w : DirectionWord n,
      StoppedNetworkTrail p.normalized p.u (insert p.v (protectedSites p.G)) w →
      wordVertex p.u w n ∈ protectedSites p.G → ∀ b : Bool,
      |(traceNetwork p.normalized (wordVertices p.u w)).expectation p.τ b
        (fun a => dot (a (wordVertex p.u w n)) (a p.v))| ≤ K) :
    |secondTerm p| ≤ (2 * K) * onePointSum p.normalized p.τ p.u := by
  classical
  unfold secondTerm onePointSum stoppedSum
  rw [Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro n _
  rw [Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  unfold stoppedNetworkTrails
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_le_sum
  intro w _
  by_cases hw : StoppedNetworkTrail p.normalized p.u (insert p.v (protectedSites p.G)) w
  · rw [ite_eq_left hw]
    by_cases he : wordVertex p.u w n = p.v
    · simp only [ite_eq_left he, abs_zero]
      split
      · exact mul_nonneg (mul_nonneg (by norm_num) hK)
          (mul_nonneg (traceCoefficient_cast_nonneg _ _) (trace_max_nonneg _ _ _))
      · exact le_rfl
    · have hS := stopped_boundary_trail p.normalized p.u p.v w hw he
      simp only [ite_eq_right he, ite_eq_left hS]
      exact weighted_response_bound _ _ _ _ _ K
        (traceCoefficient_cast_nonneg _ _) (traceRatio_nonneg _ _ _ _)
        (traceRatio_nonneg _ _ _ _) hK (hterminal n w hw hS.2.2.2 true)
        (hterminal n w hw hS.2.2.2 false)
  · simp only [ite_eq_right hw]
    split
    · exact mul_nonneg (mul_nonneg (by norm_num) hK)
        (mul_nonneg (traceCoefficient_cast_nonneg _ _) (trace_max_nonneg _ _ _))
    · exact le_rfl

end AKLT.W.REC081
