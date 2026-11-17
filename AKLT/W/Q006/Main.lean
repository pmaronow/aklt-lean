module
public import AKLT.Blueprint.Q.NodesFrames

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section

open AKLT.Defs

namespace AKLT.W.Q006

private def euclid (x : Vec3) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 x

private lemma normSq_eq_euclid_norm_sq (x : Vec3) :
    normSq x = ‖euclid x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [euclid, normSq, dot, pow_two]

private lemma normSq_sub_eq_euclid_norm_sq (x y : Vec3) :
    normSq (x - y) = ‖euclid x - euclid y‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [euclid, normSq, dot, pow_two]

private lemma normSq_sub_identity (x y : Vec3) :
    normSq (x - y) = normSq x + normSq y - 2 * dot x y := by
  unfold normSq dot
  calc
    (∑ i, (x - y) i * (x - y) i) =
        ∑ i, (x i * x i + y i * y i - 2 * (x i * y i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          simp only [Pi.sub_apply]
          ring
    _ = (∑ i, x i * x i) + (∑ i, y i * y i) -
          2 * (∑ i, x i * y i) := by
          simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]

theorem main : AKLT.Blueprint.Q.DisplacedDistanceStatement := by
  intro u v w hu hv hw huv hvw
  let U := euclid u
  let V := euclid v
  let W := euclid w
  have hUVsq : ‖U - V‖ ^ 2 = normSq (u - v) := by
    simpa [U, V] using (normSq_sub_eq_euclid_norm_sq u v).symm
  have hVWs : ‖W - V‖ ^ 2 = normSq (w - v) := by
    simpa [W, V] using (normSq_sub_eq_euclid_norm_sq w v).symm
  have hUWsq : ‖U - W‖ ^ 2 = normSq (u - w) := by
    simpa [U, W] using (normSq_sub_eq_euclid_norm_sq u w).symm
  have hUVlarge : 1 < ‖U - V‖ := by
    have hn := norm_nonneg (U - V)
    nlinarith
  have hconstant : 0 ≤ (40 : ℝ) / 101 := by positivity
  have hVWsmall : ‖W - V‖ ≤ (40 : ℝ) / 101 := by
    have hn := norm_nonneg (W - V)
    nlinarith
  have htriangle : ‖U - V‖ ≤ ‖U - W‖ + ‖W - V‖ := by
    calc
      ‖U - V‖ = ‖(U - W) + (W - V)‖ := by congr 1; abel
      _ ≤ ‖U - W‖ + ‖W - V‖ := norm_add_le _ _
  have hUWlarge : (3 : ℝ) / 5 < ‖U - W‖ := by
    have hgap : (3 : ℝ) / 5 < 1 - (40 : ℝ) / 101 := by norm_num
    linarith
  have hdistance : (9 : ℝ) / 25 < normSq (u - w) := by
    rw [← hUWsq]
    have hn := norm_nonneg (U - W)
    nlinarith
  have hidentity := normSq_sub_identity u w
  nlinarith [hdistance]

end AKLT.W.Q006
