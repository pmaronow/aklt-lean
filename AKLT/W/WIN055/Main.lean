module
public import AKLT.Blueprint.Win.NodesRemoval

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.WIN055

private def euclideanVec (v : Vec3) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 v

private lemma euclideanVec_norm_sq (v : Vec3) :
    ‖euclideanVec v‖ ^ 2 = normSq v := by
  calc
    ‖euclideanVec v‖ ^ 2 = ∑ i, (euclideanVec v i) ^ 2 :=
      EuclideanSpace.real_norm_sq_eq _
    _ = normSq v := by simp [euclideanVec, normSq, dot, pow_two]

private lemma dot_eq_euclidean_inner (a b : Vec3) :
    dot a b = inner ℝ (euclideanVec a) (euclideanVec b) := by
  simp [euclideanVec, dot, EuclideanSpace.inner_toLp_toLp, dotProduct, mul_comm]

private lemma norm_le_one_of_normSq_le_one {v : Vec3} (hv : normSq v ≤ 1) :
    ‖euclideanVec v‖ ≤ 1 := by
  have hs : ‖euclideanVec v‖ ^ 2 ≤ 1 := by
    rw [euclideanVec_norm_sq]
    exact hv
  nlinarith [sq_nonneg (‖euclideanVec v‖ - 1), norm_nonneg (euclideanVec v)]

private lemma dot_abs_le_one {a b : Vec3} (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) :
    |dot a b| ≤ 1 := by
  have ha' := norm_le_one_of_normSq_le_one ha
  have hb' := norm_le_one_of_normSq_le_one hb
  calc
    |dot a b| = |inner ℝ (euclideanVec a) (euclideanVec b)| := by
      rw [dot_eq_euclidean_inner]
    _ ≤ ‖euclideanVec a‖ * ‖euclideanVec b‖ := abs_real_inner_le_norm _ _
    _ ≤ 1 := by
      calc
        ‖euclideanVec a‖ * ‖euclideanVec b‖ ≤ 1 * ‖euclideanVec b‖ :=
          mul_le_mul_of_nonneg_right ha' (norm_nonneg _)
        _ ≤ 1 := by simpa using hb'

private lemma extendIcoSpins_normSq_le_one {V : Finset Plane}
    (hMom : AKLT.Blueprint.Top.MomentsStatement)
    (σ : PlaneConfiguration V) (z : Plane) :
    normSq (extendIcoSpins σ z) ≤ 1 := by
  by_cases hz : z ∈ V
  · rw [extendIcoSpins, dif_pos hz]
    rw [hMom.2.1]
  · rw [extendIcoSpins, dif_neg hz]
    simp [normSq, dot]

private lemma quartic_abs_le_three (hMom : AKLT.Blueprint.Top.MomentsStatement)
    {V : Finset Plane} (σ : PlaneConfiguration V) (x : Plane) :
    |AKLT.Blueprint.Win.quartic x (extendIcoSpins σ)| ≤ 3 := by
  let a := extendIcoSpins σ (x + Compass.east.step)
  let b := extendIcoSpins σ (x + Compass.west.step)
  let c := extendIcoSpins σ (x + Compass.south.step)
  let d := extendIcoSpins σ (x + Compass.north.step)
  have ha : normSq a ≤ 1 := extendIcoSpins_normSq_le_one hMom σ _
  have hb : normSq b ≤ 1 := extendIcoSpins_normSq_le_one hMom σ _
  have hc : normSq c ≤ 1 := extendIcoSpins_normSq_le_one hMom σ _
  have hd : normSq d ≤ 1 := extendIcoSpins_normSq_le_one hMom σ _
  have hab : |dot a b| ≤ 1 := dot_abs_le_one ha hb
  have hac : |dot a c| ≤ 1 := dot_abs_le_one ha hc
  have had : |dot a d| ≤ 1 := dot_abs_le_one ha hd
  have hbc : |dot b c| ≤ 1 := dot_abs_le_one hb hc
  have hbd : |dot b d| ≤ 1 := dot_abs_le_one hb hd
  have hcd : |dot c d| ≤ 1 := dot_abs_le_one hc hd
  have h₁ : |dot a b * dot c d| ≤ 1 := by
    rw [abs_mul]
    calc
      |dot a b| * |dot c d| ≤ 1 * 1 := mul_le_mul hab hcd (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have h₂ : |dot a c * dot b d| ≤ 1 := by
    rw [abs_mul]
    calc
      |dot a c| * |dot b d| ≤ 1 * 1 := mul_le_mul hac hbd (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have h₃ : |dot a d * dot b c| ≤ 1 := by
    rw [abs_mul]
    calc
      |dot a d| * |dot b c| ≤ 1 * 1 := mul_le_mul had hbc (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  change |dot a b * dot c d + dot a c * dot b d + dot a d * dot b c| ≤ 3
  calc
    |dot a b * dot c d + dot a c * dot b d + dot a d * dot b c|
        ≤ |dot a b * dot c d| + |dot a c * dot b d| + |dot a d * dot b c| := by
          calc
            |(dot a b * dot c d + dot a c * dot b d) + dot a d * dot b c|
                ≤ |dot a b * dot c d + dot a c * dot b d| + |dot a d * dot b c| :=
                  abs_add_le _ _
            _ ≤ |dot a b * dot c d| + |dot a c * dot b d| +
                |dot a d * dot b c| := by
                  have habs := abs_add_le (dot a b * dot c d) (dot a c * dot b d)
                  linarith
    _ ≤ 3 := by linarith

theorem main : AKLT.Blueprint.Win.QuarticMeanBoundStatement := by
  intro hMom D p hp x
  rcases hp with ⟨hp_nonneg, hp_sum⟩
  change |∑ σ : PlaneConfiguration D,
      p σ * AKLT.Blueprint.Win.quartic x (extendIcoSpins σ)| ≤ 3
  calc
    |∑ σ : PlaneConfiguration D,
        p σ * AKLT.Blueprint.Win.quartic x (extendIcoSpins σ)|
        ≤ ∑ σ : PlaneConfiguration D,
          |p σ * AKLT.Blueprint.Win.quartic x (extendIcoSpins σ)| :=
            Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ σ : PlaneConfiguration D, p σ * 3 := by
      apply Finset.sum_le_sum
      intro σ _
      rw [abs_mul, abs_of_nonneg (hp_nonneg σ)]
      exact mul_le_mul_of_nonneg_left (quartic_abs_le_three hMom σ x) (hp_nonneg σ)
    _ = 3 := by rw [← Finset.sum_mul, hp_sum]; norm_num

end AKLT.W.WIN055
