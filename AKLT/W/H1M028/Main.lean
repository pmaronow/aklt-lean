module
public import AKLT.Blueprint.H1.NodesReduction

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.H1M028

private lemma normSq_nonneg (v : Vec3) : 0 ≤ normSq v := by
  unfold normSq dot
  exact Finset.sum_nonneg fun i hi => mul_self_nonneg (v i)

private lemma normSq_div (v : Vec3) (r : ℝ) :
    normSq (fun i => v i / r) = normSq v / r ^ 2 := by
  unfold normSq dot
  simp only [div_eq_mul_inv]
  have hinv : r⁻¹ * r⁻¹ = (r ^ 2)⁻¹ := by
    rw [← pow_two, inv_pow]
  calc
    (∑ i, v i * r⁻¹ * (v i * r⁻¹)) =
        ∑ i, (v i * v i) * (r⁻¹ * r⁻¹) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (∑ i, v i * v i) * (r⁻¹ * r⁻¹) := by
      rw [Finset.sum_mul]
    _ = (∑ i, v i * v i) * (r ^ 2)⁻¹ := by rw [hinv]

private lemma normSq_eq_zero_iff (v : Vec3) : normSq v = 0 ↔ v = 0 := by
  constructor
  · intro hv
    funext i
    have hs : v i * v i ≤ normSq v := by
      unfold normSq dot
      exact Finset.single_le_sum
        (fun j hj => mul_self_nonneg (v j)) (Finset.mem_univ i)
    have hsqzero : v i * v i = 0 := by
      rw [hv] at hs
      nlinarith [sq_nonneg (v i)]
    exact (mul_self_eq_zero.mp hsqzero)
  · intro hv
    simp [hv, normSq, dot]

private def axis : Vec3 := fun i => if i = 0 then 1 else 0

private lemma axis_normSq : normSq axis = 1 := by
  norm_num [normSq, dot, axis]

theorem main : AKLT.Blueprint.H1.BallChordStatement := by
  intro v hv
  by_cases hzero : normSq v = 0
  · have hv0 : v = 0 := (normSq_eq_zero_iff v).mp hzero
    subst v
    refine ⟨⟨axis, axis_normSq⟩, ⟨fun i => -axis i, ?_⟩, (1 / 2 : ℝ), by norm_num, by norm_num, ?_⟩
    · simp [normSq, dot, axis]
    · ext i
      by_cases hi : i = 0
      · norm_num [axis, hi]
      · simp [axis, hi]
  · have hq : 0 < normSq v := lt_of_le_of_ne (normSq_nonneg v) (Ne.symm hzero)
    let r : ℝ := Real.sqrt (normSq v)
    have hr0 : 0 ≤ r := by
      exact Real.sqrt_nonneg _
    have hrpos : 0 < r := by
      dsimp [r]
      exact Real.sqrt_pos.2 hq
    have hr2 : r ^ 2 = normSq v := by
      dsimp [r]
      exact Real.sq_sqrt (le_of_lt hq)
    have hrle : r ≤ 1 := by
      nlinarith [hv, hr0, hr2]
    let w : Vec3 := fun i => v i / r
    have hw : normSq w = 1 := by
      dsimp [w]
      rw [normSq_div, hr2]
      exact div_self (ne_of_gt hq)
    let t : ℝ := (1 + r) / 2
    have ht0 : 0 ≤ t := by
      dsimp [t]
      linarith
    have ht1 : t ≤ 1 := by
      dsimp [t]
      linarith
    have hcoord : v = t • w + (1 - t) • (fun i => -w i) := by
      funext i
      symm
      change t * (v i / r) + (1 - t) * (-(v i / r)) = v i
      have htr : 2 * t - 1 = r := by dsimp [t]; ring
      calc
        _ = (t - (1 - t)) * (v i / r) := by ring
        _ = r * (v i / r) := by rw [show t - (1 - t) = r by linarith [htr]]
        _ = v i := by field_simp [ne_of_gt hrpos]
    exact ⟨⟨w, hw⟩, ⟨fun i => -w i, by
      have hneg : normSq (fun i => -w i) = normSq w := by
        simp [normSq, dot]
      rw [hneg, hw]⟩, t, ht0, ht1, hcoord⟩

end AKLT.W.H1M028
