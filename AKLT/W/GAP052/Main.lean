import AKLT.Blueprint.Gap.NodesShell

noncomputable section

open AKLT.Blueprint.Gap

namespace AKLT.W.GAP052

/-- Choose a natural scale above all four archimedean thresholds. -/
theorem main : AKLT.Blueprint.Gap.ScaleExistenceStatement := by
  intro l Mstar d hd
  let C : ℝ := (50000 : ℝ) * 2^20 * (Nat.factorial 20 : ℝ)
  let K : ℝ := max 50000 (6 * ((l + 1 : ℕ) : ℝ))
  let B : ℝ := max 44 (max (Mstar : ℝ) (max K (C / d^20)))
  have hd20 : 0 < d^20 := by positivity
  have hCdiv : 0 < C / d^20 := by
    apply div_pos
    · dsimp [C]
      positivity
    · exact hd20
  obtain ⟨n, hn⟩ := exists_nat_gt B
  have h44B : (44 : ℝ) ≤ B := by
    dsimp [B]
    exact le_max_left _ _
  have hMB : (Mstar : ℝ) ≤ B := by
    dsimp [B]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hKB : K ≤ B := by
    dsimp [B]
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hCB : C / d^20 ≤ B := by
    dsimp [B]
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hn44 : 44 ≤ n := by
    exact_mod_cast (le_of_lt (lt_of_le_of_lt h44B hn))
  have hnM : Mstar ≤ n := by
    exact_mod_cast (le_of_lt (lt_of_le_of_lt hMB hn))
  have hnK : max 50000 (6 * (l + 1)) ≤ n := by
    change (max 50000 (6 * ((l + 1 : ℕ) : ℝ)) : ℝ) ≤ B at hKB
    exact_mod_cast (le_of_lt (lt_of_le_of_lt hKB hn))
  have hn_one : 1 ≤ n := by omega
  have hn8 : n ≤ n^8 := by
    exact le_self_pow hn_one (by norm_num)
  have hn2 : n ≤ n^2 := by
    exact le_self_pow hn_one (by norm_num)
  have hn12R : (n : ℝ) ≤ (n : ℝ)^12 := by
    exact le_self_pow₀ (by exact_mod_cast hn_one) (by norm_num)
  have hlast : C ≤ (n : ℝ)^12 * d^20 := by
    apply (div_le_iff₀ hd20).mp
    exact le_trans hCB (le_trans (le_of_lt hn) hn12R)
  refine ⟨n, ?_⟩
  exact ⟨hn44, Nat.le_trans hnM hn8, Nat.le_trans hnK hn2, by simpa [C] using hlast⟩

end AKLT.W.GAP052
