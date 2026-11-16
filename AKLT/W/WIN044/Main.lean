import AKLT.Blueprint.Win.NodesTaper

noncomputable section
open scoped BigOperators

namespace AKLT.W.WIN044

theorem main : AKLT.Blueprint.Win.NearSeriesStatement := by
  intro θ hθ0 hθ1
  let f : ℕ → ℝ := fun j => θ ^ (max j 16 - 2)
  have hgeom : Summable (fun j : ℕ => θ ^ j) :=
    summable_geometric_of_lt_one hθ0.le hθ1
  have htail : Summable (fun j : ℕ => θ ^ (j + 15)) := by
    simpa [pow_add, mul_comm] using hgeom.mul_left (θ ^ 15)
  have hs : Summable f := by
    apply (summable_nat_add_iff (f := f) 17).mp
    convert htail using 1
    funext j
    dsimp [f]
    congr 1
  constructor
  · exact hs
  · have hfirst : ∑ j ∈ Finset.range 17, f j = 17 * θ ^ 14 := by
      calc
        ∑ j ∈ Finset.range 17, f j =
            ∑ j ∈ Finset.range 17, θ ^ 14 := by
              apply Finset.sum_congr rfl
              intro j hj
              dsimp [f]
              have hj' : j ≤ 16 := by simp only [Finset.mem_range] at hj; omega
              simp [max_eq_right hj']
        _ = 17 * θ ^ 14 := by simp
    have htailSum : (∑' j : ℕ, f (j + 17)) = θ ^ 15 * (1 - θ)⁻¹ := by
      calc
        (∑' j : ℕ, f (j + 17)) = ∑' j : ℕ, θ ^ (j + 15) := by
          apply tsum_congr
          intro j
          dsimp [f]
          congr 1
        _ = θ ^ 15 * (1 - θ)⁻¹ := by
          rw [show (fun j : ℕ => θ ^ (j + 15)) =
              fun j => θ ^ 15 * θ ^ j by
                funext j
                rw [pow_add]
                exact mul_comm _ _]
          rw [tsum_mul_left, tsum_geometric_of_lt_one hθ0.le hθ1]
    have htotal : (∑' j : ℕ, f j) =
        17 * θ ^ 14 + θ ^ 15 * (1 - θ)⁻¹ := by
      rw [← hs.sum_add_tsum_nat_add 17, hfirst, htailSum]
    have hfrac : θ / (1 - θ) ≤ 1 / (1 - θ) := by
      exact div_le_div_of_nonneg_right (le_of_lt hθ1) (le_of_lt (sub_pos.mpr hθ1))
    rw [htotal, AKLT.Blueprint.Win.nearCost]
    have hfactor : 0 ≤ 48 * θ ^ 14 := by positivity
    have hrewrite : 17 * θ ^ 14 + θ ^ 15 * (1 - θ)⁻¹ =
        θ ^ 14 * (17 + θ / (1 - θ)) := by
      have hden : 1 - θ ≠ 0 := ne_of_gt (sub_pos.mpr hθ1)
      field_simp [hden]
    rw [hrewrite]
    have hineq : 17 + θ / (1 - θ) ≤ 17 + 1 / (1 - θ) := by linarith
    calc
      48 * (θ ^ 14 * (17 + θ / (1 - θ))) =
          (48 * θ ^ 14) * (17 + θ / (1 - θ)) := by ring
      _ ≤ (48 * θ ^ 14) * (17 + 1 / (1 - θ)) :=
        mul_le_mul_of_nonneg_left hineq hfactor
      _ = 48 * θ ^ 14 * (17 + 1 / (1 - θ)) := by ring

end AKLT.W.WIN044
