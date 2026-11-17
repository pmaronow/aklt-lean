module
public import AKLT.Blueprint.Gap.NodesShell

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section

namespace AKLT.W.GAP056

open AKLT.Blueprint.Gap

theorem main : AKLT.Blueprint.Gap.HammingBudgetStatement := by
  intro l Mstar d n hd hdup hScale hTail
  rcases hScale with ⟨hn, hM, hScaleN, hMoment⟩
  have hn0 : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
  have hn2N : 50000 ≤ n ^ 2 := by
    exact le_trans (Nat.le_max_left _ _) hScaleN
  have hn2 : (50000 : ℝ) ≤ (n : ℝ) ^ 2 := by
    exact_mod_cast hn2N
  let C : ℝ := (2 ^ 20 : ℝ) * (Nat.factorial 20 : ℝ)
  have hFirst : 25 * (n : ℝ) ^ 6 ≤ (n : ℝ) ^ 8 / 2000 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2000)]
    have hmul := mul_le_mul_of_nonneg_left hn2 (by positivity : 0 ≤ (n : ℝ) ^ 6)
    nlinarith [hmul]
  have hDenA : 0 < d ^ 20 * (n : ℝ) ^ 20 := by positivity
  have hDenB : 0 < (50000 : ℝ) * (n : ℝ) ^ 8 := by positivity
  have hMoment' : 50000 * C ≤ (n : ℝ) ^ 12 * d ^ 20 := by
    simpa [C, mul_assoc, mul_left_comm, mul_comm] using hMoment
  have hProduct : C * (50000 * (n : ℝ) ^ 8) ≤ d ^ 20 * (n : ℝ) ^ 20 := by
    have hmul := mul_le_mul_of_nonneg_right hMoment' (by positivity : 0 ≤ (n : ℝ) ^ 8)
    nlinarith [hmul]
  have hFrac : C / (d ^ 20 * (n : ℝ) ^ 20) ≤ 1 / ((50000 : ℝ) * (n : ℝ) ^ 8) := by
    apply (div_le_div_iff₀ hDenA hDenB).2
    simpa [mul_assoc, mul_left_comm, mul_comm] using hProduct
  have hTail' : (1 - d) ^ (n - 3) ≤ 1 / ((50000 : ℝ) * (n : ℝ) ^ 8) := by
    calc
      (1 - d) ^ (n - 3) ≤ C / (d ^ 20 * (n : ℝ) ^ 20) := by
        simpa [C, mul_assoc, mul_left_comm, mul_comm] using hTail
      _ ≤ 1 / ((50000 : ℝ) * (n : ℝ) ^ 8) := hFrac
  have hSecond : 25 * (n : ℝ) ^ 16 * (1 - d) ^ (n - 3) ≤ (n : ℝ) ^ 8 / 2000 := by
    calc
      25 * (n : ℝ) ^ 16 * (1 - d) ^ (n - 3)
          ≤ 25 * (n : ℝ) ^ 16 * (1 / ((50000 : ℝ) * (n : ℝ) ^ 8)) := by
            exact mul_le_mul_of_nonneg_left hTail' (by positivity)
      _ = (n : ℝ) ^ 8 / 2000 := by
            field_simp
            ring
  have hAdd := add_le_add hFirst hSecond
  calc
    25 * (n : ℝ) ^ 6 + 25 * (n : ℝ) ^ 16 * (1 - d) ^ (n - 3)
        ≤ (n : ℝ) ^ 8 / 2000 + (n : ℝ) ^ 8 / 2000 := hAdd
    _ = ((n ^ 8 : ℕ) : ℝ) / 1000 := by
          norm_cast
          ring

end AKLT.W.GAP056

#print axioms AKLT.W.GAP056.main
