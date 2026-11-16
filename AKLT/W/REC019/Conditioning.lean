import AKLT.W.REC019.SpinGeometry

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC019

/-- Finite averaging, allowing zero-mass fibres and a zero total mass. -/
theorem finite_weighted_bounds {Ω : Type*} [Fintype Ω] (w F : Ω → ℝ)
    (hw : ∀ σ, 0 ≤ w σ) {l u : ℝ} (hl : l ≤ 0) (hu : 0 ≤ u)
    (hF : ∀ σ, l ≤ F σ ∧ F σ ≤ u) :
    l ≤ (∑ σ, w σ * F σ) / (∑ σ, w σ) ∧
      (∑ σ, w σ * F σ) / (∑ σ, w σ) ≤ u := by
  have hmass : 0 ≤ ∑ σ, w σ := Finset.sum_nonneg fun σ hσ => hw σ
  have hlo : l * (∑ σ, w σ) ≤ ∑ σ, w σ * F σ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro σ hσ
    simpa only [mul_comm l] using mul_le_mul_of_nonneg_left (hF σ).1 (hw σ)
  have hup : (∑ σ, w σ * F σ) ≤ u * (∑ σ, w σ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro σ hσ
    simpa only [mul_comm u] using mul_le_mul_of_nonneg_left (hF σ).2 (hw σ)
  by_cases hz : (∑ σ, w σ) = 0
  · simpa only [hz, div_zero] using And.intro hl hu
  · have hp : 0 < ∑ σ, w σ := lt_of_le_of_ne hmass (Ne.symm hz)
    exact ⟨(le_div_iff₀ hp).mpr hlo, (div_le_iff₀ hp).mpr hup⟩

def mixturePair {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)
    (m : Ω → Fin 3 → Vec3) (i j : Fin 3) : ℝ :=
  (∑ σ, w σ * dot (m σ i) (m σ j)) / (∑ σ, w σ)

theorem mixture_pair_bounds {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)
    (m : Ω → Fin 3 → Vec3) (hw : ∀ σ, 0 ≤ w σ)
    (hm : ∀ σ i, normSq (m σ i) ≤ 9 / 25) (i j : Fin 3) :
    -(9 / 25 : ℝ) ≤ mixturePair w m i j ∧ mixturePair w m i j ≤ 9 / 25 := by
  exact finite_weighted_bounds w _ hw (by norm_num) (by norm_num)
    (fun σ => dot_small_ball_bounds (hm σ i) (hm σ j))

theorem mixture_triple_lower {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)
    (m : Ω → Fin 3 → Vec3) (hw : ∀ σ, 0 ≤ w σ)
    (hm : ∀ σ i, normSq (m σ i) ≤ 9 / 25) :
    -(27 / 50 : ℝ) ≤ mixturePair w m 0 1 + mixturePair w m 0 2 + mixturePair w m 1 2 := by
  have h := finite_weighted_bounds w
    (fun σ => dot (m σ 0) (m σ 1) + dot (m σ 0) (m σ 2) + dot (m σ 1) (m σ 2))
    hw (by norm_num : -(27 / 50 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 27 / 25)
    (fun σ => And.intro (sum_three_dot_lower (hm σ 0) (hm σ 1) (hm σ 2)) (by
      have h01 := (dot_small_ball_bounds (hm σ 0) (hm σ 1)).2
      have h02 := (dot_small_ball_bounds (hm σ 0) (hm σ 2)).2
      have h12 := (dot_small_ball_bounds (hm σ 1) (hm σ 2)).2
      linarith))
  simpa only [mixturePair, mul_add, Finset.sum_add_distrib, add_div] using h.1

end AKLT.W.REC019
