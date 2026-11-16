import AKLT.Blueprint.Win.NodesShell

noncomputable section
open AKLT.Defs

namespace AKLT.W.WIN001

 theorem main : AKLT.Blueprint.Win.ShellScaleStatement := by
  intro l u hl hu
  let T : ℝ := (max 16 (6 * (l + 1)) : ℕ)
  let s : ℝ := shellSpacing u
  have hT0 : 0 ≤ T := by
    dsimp [T]
    positivity
  have hpowN : (max 16 (6 * (l + 1))) ^ 4 ≤ u := hu
  have hpow : T ^ 4 ≤ (u : ℝ) := by
    dsimp [T]
    exact_mod_cast hpowN
  have hs2 : s ^ 2 = Real.sqrt (u : ℝ) := by
    dsimp [s, shellSpacing]
    rw [Real.sq_sqrt (Real.sqrt_nonneg _)]
  have hs4 : s ^ 4 = (u : ℝ) := by
    calc
      s ^ 4 = (s ^ 2) ^ 2 := by ring
      _ = (Real.sqrt (u : ℝ)) ^ 2 := by rw [hs2]
      _ = (u : ℝ) := Real.sq_sqrt (Nat.cast_nonneg u)
  have hT2 : T ^ 2 ≤ Real.sqrt (u : ℝ) := by
    calc
      T ^ 2 = Real.sqrt (T ^ 4) := by
        rw [show T ^ 4 = (T ^ 2) ^ 2 by ring, Real.sqrt_sq_eq_abs]
        simp [abs_of_nonneg (sq_nonneg T)]
      _ ≤ Real.sqrt (u : ℝ) := Real.sqrt_le_sqrt hpow
  have hTs : T ≤ s := by
    dsimp [s, shellSpacing]
    calc
      T = Real.sqrt (T ^ 2) := by
        rw [Real.sqrt_sq_eq_abs]
        simp [abs_of_nonneg hT0]
      _ ≤ Real.sqrt (Real.sqrt (u : ℝ)) := Real.sqrt_le_sqrt hT2
  have hs16 : 16 ≤ s := by
    have h16T : (16 : ℝ) ≤ T := by
      dsimp [T]
      exact_mod_cast (le_max_left 16 (6 * (l + 1)))
    linarith
  have h6l : 6 * ((l : ℝ) + 1) ≤ s := by
    have h6T : (6 * ((l : ℝ) + 1)) ≤ T := by
      dsimp [T]
      have hle : 6 * (l + 1) ≤ max 16 (6 * (l + 1)) := le_max_right _ _
      exact_mod_cast hle
    linarith
  have hs2large : (256 : ℝ) ≤ s ^ 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ s - 16) (by linarith : 0 ≤ s + 16)]
  have hs4large : 256 * s ^ 2 ≤ s ^ 4 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ s ^ 2 - 256) (sq_nonneg s)]
  have hlow1 : s ^ 2 + 4 * s / 3 < s ^ 4 := by
    nlinarith
  have hlow2 : s ^ 2 + s < s ^ 4 / 2 := by
    nlinarith
  have hlow1u : s ^ 2 + 4 * s / 3 < (u : ℝ) := by
    rw [← hs4]
    exact hlow1
  have hlow2u : s ^ 2 + s < (u : ℝ) / 2 := by
    rw [← hs4]
    exact hlow2
  refine ⟨?_, ?_, hs4, ?_, ?_, ?_⟩
  · exact hs16
  · exact h6l
  · simpa [s] using hlow1u
  · simpa [s] using hlow2u
  · have hfloor : s < (⌊s⌋ : ℤ) + 1 := Int.lt_floor_add_one s
    have hslarge : (3 : ℝ) < s := by linarith
    linarith

end AKLT.W.WIN001
