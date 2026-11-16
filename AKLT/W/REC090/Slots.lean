import AKLT.W.REC090.Positivity

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC090

/-- A ball field, including a missing factor represented by zero, is a convex
mixture of two opposite unit fields. -/
theorem ball_slot_convexity (b : Vec3) (hb : normSq b ≤ 1) :
    ∃ e : UnitVector, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ ∀ n : Vec3,
      1 + dot n b = t * (1 + dot n e.val) + (1 - t) * (1 + dot n (-e.val)) := by
  by_cases hz : b = 0
  · subst b
    refine ⟨⟨![1, 0, 0], by norm_num [normSq, dot, Fin.sum_univ_succ]⟩, 1 / 2,
      by norm_num, by norm_num, ?_⟩
    intro n
    simp [dot, Fin.sum_univ_succ]
    ring
  · let r := Real.sqrt (normSq b)
    have hr2 : r ^ 2 = normSq b := Real.sq_sqrt (normSq_nonneg b)
    have hr : 0 < r := by
      apply Real.sqrt_pos.mpr
      exact lt_of_le_of_ne (normSq_nonneg b) fun h => hz (normSq_eq_zero h.symm)
    have hr1 : r ≤ 1 := by nlinarith
    let e : UnitVector := ⟨fun i => b i / r, by
      change (∑ i, (b i / r) * (b i / r)) = 1
      simp only [div_mul_div_comm, ← Finset.sum_div]
      change normSq b / (r * r) = 1
      rw [← pow_two, hr2]
      exact div_self (ne_of_gt (by nlinarith : 0 < normSq b))⟩
    refine ⟨e, (1 + r) / 2, by positivity, by linarith, ?_⟩
    intro n
    have hn : dot n b = r * dot n e.val := by
      dsimp [e, dot]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      field_simp
    have hneg : dot n (-e.val) = -dot n e.val := by
      simp [dot, Finset.sum_neg_distrib]
    rw [hneg, hn]
    ring

/-- Resolve any finite family of ball slots simultaneously, with coefficients
that do not depend on the local spin configuration. -/
theorem ball_slots_mixture {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ι → Vec3)
    (hb : ∀ j, normSq (b j) ≤ 1) :
    ∃ m : (ι → Bool) → ι → UnitVector, ∃ weight : (ι → Bool) → ℝ,
      (∀ σ, 0 ≤ weight σ) ∧ (∑ σ, weight σ) = 1 ∧
      ∀ n : ι → Vec3, (∏ j, (1 + dot (n j) (b j))) =
        ∑ σ, weight σ * ∏ j, (1 + dot (n j) (m σ j).val) := by
  classical
  choose e t ht ht1 he using fun j => ball_slot_convexity (b j) (hb j)
  let p : ι → Bool → ℝ := fun j s => if s then t j else 1 - t j
  let m : (ι → Bool) → ι → UnitVector := fun σ j =>
    if σ j then e j else ⟨-(e j).val, by
      change (∑ i, (-(e j).val i) * (-(e j).val i)) = 1
      simp only [neg_mul_neg]
      exact (e j).property⟩
  let weight : (ι → Bool) → ℝ := fun σ => ∏ j, p j (σ j)
  refine ⟨m, weight, ?_, ?_, ?_⟩
  · intro σ
    exact Finset.prod_nonneg fun j _ => by
      dsimp [p]
      split
      · exact ht j
      · linarith [ht1 j]
  · dsimp [weight]
    rw [← Fintype.prod_sum]
    simp [p]
  · intro n
    have hf : ∀ j, 1 + dot (n j) (b j) =
        ∑ s : Bool, p j s * (1 + dot (n j) (m (fun _ => s) j).val) := by
      intro j
      simpa [p, m, add_comm] using he j (n j)
    simp_rw [hf]
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro σ _
    dsimp [weight]
    rw [← Finset.prod_mul_distrib]

end AKLT.W.REC090
