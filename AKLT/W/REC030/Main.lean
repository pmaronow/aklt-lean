import AKLT.Blueprint.Rec.NodesLocal

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC030

private theorem dot_smul_right (a b : Vec3) (c : ℝ) :
    dot a (c • b) = c * dot a b := by
  unfold dot
  simp only [Pi.smul_apply]
  calc
    (∑ i : Fin 3, a i * (c * b i)) = ∑ i : Fin 3, c * (a i * b i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = c * ∑ i : Fin 3, a i * b i := by rw [Finset.mul_sum]

private theorem normSq_div (v : Vec3) (c : ℝ) :
    normSq (fun i => v i / c) = normSq v / c ^ 2 := by
  simp only [normSq, dot, div_mul_div_comm, ← Finset.sum_div, pow_two]

private theorem vec_eq_zero_of_normSq_eq_zero (v : Vec3)
    (h : normSq v = 0) : v = 0 := by
  funext i
  have hle : v i * v i ≤ normSq v := by
    unfold normSq dot
    exact Finset.single_le_sum
      (s := Finset.univ) (f := fun j : Fin 3 => v j * v j)
      (fun j _ => mul_self_nonneg (v j)) (Finset.mem_univ i)
  rw [h] at hle
  have hsquare : 0 ≤ v i * v i := mul_self_nonneg (v i)
  have hmul : v i * v i = 0 := le_antisymm hle hsquare
  rcases mul_eq_zero.mp hmul with hi | hi <;> exact hi

private def fallbackVector : Vec3 := fun i => if i = 0 then 1 else 0

private theorem fallbackVector_unit : normSq fallbackVector = 1 := by
  norm_num [fallbackVector, normSq, dot]

theorem main : AKLT.Blueprint.Rec.BallSlotConvexityStatement := by
  intro b hb
  let q : ℝ := normSq b
  have hq_nonneg : 0 ≤ q := by
    dsimp [q, normSq, dot]
    apply Finset.sum_nonneg
    intro i hi
    exact mul_self_nonneg (b i)
  have hr_nonneg : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  have hr_sq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq_nonneg
  have hr_le_one : Real.sqrt q ≤ 1 := by
    dsimp [q] at hr_sq ⊢
    nlinarith [hb]
  let t : ℝ := (1 + Real.sqrt q) / 2
  have ht_nonneg : 0 ≤ t := by dsimp [t]; linarith
  have ht_le_one : t ≤ 1 := by dsimp [t]; linarith
  have hscale : 2 * t - 1 = Real.sqrt q := by
    dsimp [t]
    ring
  let ev : Vec3 := if hz : q = 0 then fallbackVector else fun i => b i / Real.sqrt q
  have hev_unit : normSq ev = 1 := by
    by_cases hz : q = 0
    · simp [ev, hz, fallbackVector_unit]
    · have hq_pos : 0 < q := lt_of_le_of_ne hq_nonneg (Ne.symm hz)
      have hr_pos : 0 < Real.sqrt q := Real.sqrt_pos.2 hq_pos
      rw [show ev = (fun i => b i / Real.sqrt q) by simp [ev, hz]]
      rw [normSq_div]
      rw [show (Real.sqrt q) ^ 2 = normSq b by simpa [q] using hr_sq]
      exact div_self (ne_of_gt (by simpa [q] using hq_pos))
  have hvec : b = (2 * t - 1) • ev := by
    funext i
    by_cases hz : q = 0
    · have hbi : b i = 0 := by
        apply congrFun (vec_eq_zero_of_normSq_eq_zero b (by simpa [q] using hz))
      simp [ev, hz, hbi, hscale]
    · have hq_pos : 0 < q := lt_of_le_of_ne hq_nonneg (Ne.symm hz)
      have hr_pos : 0 < Real.sqrt q := Real.sqrt_pos.2 hq_pos
      rw [show ev = (fun j => b j / Real.sqrt q) by simp [ev, hz]]
      simp only [Pi.smul_apply]
      rw [hscale]
      change b i = Real.sqrt q * (b i / Real.sqrt q)
      field_simp [ne_of_gt hr_pos]
  refine ⟨⟨ev, hev_unit⟩, t, ht_nonneg, ht_le_one, ?_⟩
  intro n
  have hdot : dot n b = (2 * t - 1) * dot n ev := by
    rw [hvec, dot_smul_right]
  have hneg : dot n (-ev) = -dot n ev := by
    unfold dot
    simp only [Pi.neg_apply, mul_neg]
    rw [Finset.sum_neg_distrib]
  rw [hdot, hneg]
  rw [hscale]
  dsimp [t]
  ring

end AKLT.W.REC030

end
