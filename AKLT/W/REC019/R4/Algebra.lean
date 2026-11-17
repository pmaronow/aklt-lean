import AKLT.Blueprint.Rec.NodesResponse

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC019.R4

lemma normSq_nonneg (v : Vec3) : 0 ≤ normSq v := by
  change 0 ≤ ∑ i, v i * v i
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))

lemma dot_comm (v w : Vec3) : dot v w = dot w v := by
  unfold dot
  congr 1
  ext i
  exact mul_comm _ _

lemma dot_sq_le (v w : Vec3) : (dot v w)^2 ≤ normSq v * normSq w := by
  simpa [dot, normSq, pow_two] using
    Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3)) v w

lemma dot_bounds {v w : Vec3} {r : ℝ} (hr : 0 ≤ r)
    (hv : normSq v ≤ r) (hw : normSq w ≤ r) : -r ≤ dot v w ∧ dot v w ≤ r := by
  have h := dot_sq_le v w
  have hp : normSq v * normSq w ≤ r * r :=
    mul_le_mul hv hw (normSq_nonneg w) hr
  constructor <;> nlinarith

lemma triple_dot_bounds {u v w : Vec3}
    (hu : normSq u ≤ 9 / 25) (hv : normSq v ≤ 9 / 25)
    (hw : normSq w ≤ 9 / 25) :
    -(27 / 50 : ℝ) ≤ dot u v + dot u w + dot v w ∧
      dot u v + dot u w + dot v w ≤ 27 / 25 := by
  have huv := dot_bounds (by norm_num : (0 : ℝ) ≤ 9 / 25) hu hv
  have huw := dot_bounds (by norm_num : (0 : ℝ) ≤ 9 / 25) hu hw
  have hvw := dot_bounds (by norm_num : (0 : ℝ) ≤ 9 / 25) hv hw
  have hz := normSq_nonneg (u + v + w)
  have he : normSq (u + v + w) = normSq u + normSq v + normSq w +
      2 * (dot u v + dot u w + dot v w) := by
    simp [normSq, dot, Pi.add_apply, Fin.sum_univ_three]
    ring
  constructor <;> nlinarith

/-- An unnormalized finite average preserves an interval, including mass zero. -/
lemma quotient_interval {α : Type*} [Fintype α] (w x : α → ℝ) (l u : ℝ)
    (hw : ∀ a, 0 ≤ w a) (hl : l ≤ 0) (hu : 0 ≤ u)
    (hx : ∀ a, l * w a ≤ x a ∧ x a ≤ u * w a) :
    l ≤ (∑ a, x a) / (∑ a, w a) ∧
      (∑ a, x a) / (∑ a, w a) ≤ u := by
  have hW : 0 ≤ ∑ a, w a := Finset.sum_nonneg (fun a _ => hw a)
  have hL : l * (∑ a, w a) ≤ ∑ a, x a := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun a _ => (hx a).1)
  have hU : (∑ a, x a) ≤ u * (∑ a, w a) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun a _ => (hx a).2)
  rcases eq_or_lt_of_le hW with hZ | hP
  · rw [← hZ, div_zero]
    exact ⟨hl, hu⟩
  · exact ⟨(le_div_iff₀ hP).2 hL, (div_le_iff₀ hP).2 hU⟩


end AKLT.W.REC019.R4
