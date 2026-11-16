import AKLT.Blueprint.Gap.NodesShell

noncomputable section
open AKLT.Defs AKLT.Blueprint.Gap

namespace AKLT.W.GAP054

theorem shellSpacing_eighth (n : ℕ) : shellSpacing (n ^ 8) = (n : ℝ) ^ 2 := by
  unfold shellSpacing
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  calc
    Real.sqrt (Real.sqrt ((n ^ 8 : ℕ) : ℝ)) =
        Real.sqrt (Real.sqrt (((n : ℝ) ^ 4) ^ 2)) := by
          congr 2
          norm_cast
          ring
    _ = (n : ℝ) ^ 2 := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) ^ 4)]
      rw [show (n : ℝ) ^ 4 = ((n : ℝ) ^ 2) ^ 2 by ring]
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) ^ 2)]

theorem main : AKLT.Blueprint.Gap.ScaleGeometryStatement := by
  intro l Mstar d n hscale
  rcases hscale with ⟨hn44, hMstar, hn2, _⟩
  have h16n : 16 ≤ n := by omega
  have h1n : 1 ≤ n := by omega
  have h16sq : 16 ≤ n ^ 2 := by
    calc
      16 = 16 * 1 := by norm_num
      _ ≤ n * n := Nat.mul_le_mul h16n h1n
      _ = n ^ 2 := by simp [pow_two]
  have hbase : max 16 (6 * (l + 1)) ≤ n ^ 2 := by
    apply max_le
    · exact h16sq
    · calc
        6 * (l + 1) ≤ max 50000 (6 * (l + 1)) := le_max_right 50000 (6 * (l + 1))
        _ ≤ n ^ 2 := hn2
  have hgeom : geometryThreshold l ≤ n ^ 8 := by
    calc
      geometryThreshold l = (max 16 (6 * (l + 1))) ^ 4 := rfl
      _ ≤ (n ^ 2) ^ 4 := Nat.pow_le_pow_left hbase 4
      _ = n ^ 8 := by rw [← pow_mul]
  have hs : shellSpacing (n ^ 8) = (n : ℝ) ^ 2 := shellSpacing_eighth n
  have hnR : (44 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn44
  refine ⟨max_le hMstar hgeom, by omega, ?_, ?_, ?_⟩
  · rw [hs]
    nlinarith
  · rw [hs]
    ring
  · rw [hs]
    nlinarith

#print axioms main

end AKLT.W.GAP054
