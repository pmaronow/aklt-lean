module
public import AKLT.Blueprint.Win.NodesTaper

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section

namespace AKLT.W.WIN031

open AKLT.Defs
open AKLT.Blueprint.Win

theorem main : AKLT.Blueprint.Win.CutScalesStatement := by
  intro a y u i hsetup
  rcases hsetup with ⟨hshell, hi2, his, _⟩
  have huThreshold : geometryThreshold 64 ≤ u := hshell.2.1
  have hu390 : 390 ^ 4 ≤ u := by
    norm_num [geometryThreshold] at huThreshold ⊢
    exact huThreshold
  have hu0 : 0 ≤ (u : ℝ) := Nat.cast_nonneg _
  have hsqrt0 : 0 ≤ Real.sqrt (u : ℝ) := Real.sqrt_nonneg _
  have hs0 : 0 ≤ shellSpacing u := Real.sqrt_nonneg _
  have hs2 : (shellSpacing u) ^ 2 = Real.sqrt (u : ℝ) := by
    unfold shellSpacing
    exact Real.sq_sqrt hsqrt0
  have huSq : (Real.sqrt (u : ℝ)) ^ 2 = (u : ℝ) := Real.sq_sqrt hu0
  have hs4 : (shellSpacing u) ^ 4 = (u : ℝ) := by
    calc
      (shellSpacing u) ^ 4 = ((shellSpacing u) ^ 2) ^ 2 := by ring
      _ = (Real.sqrt (u : ℝ)) ^ 2 := by rw [hs2]
      _ = (u : ℝ) := huSq
  have hu390R : (390 : ℝ) ^ 4 ≤ (u : ℝ) := by exact_mod_cast hu390
  have h390sq : (390 : ℝ) ^ 2 ≤ Real.sqrt (u : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hs390 : (390 : ℝ) ≤ shellSpacing u := by
    unfold shellSpacing
    apply Real.le_sqrt_of_sq_le
    exact h390sq
  have hi2R : (2 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi2
  have hisR : (i : ℝ) ≤ shellSpacing u := his
  let r : ℝ := (shellRadius u i : ℝ)
  have hfloorLE : r ≤ (i : ℝ) * shellSpacing u := by
    dsimp [r, shellRadius]
    exact Int.floor_le _
  have hfloorLT : (i : ℝ) * shellSpacing u < r + 1 := by
    dsimp [r, shellRadius]
    simp
  have hirange : (i : ℝ) * shellSpacing u ≤ (shellSpacing u) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr (hisR)) hs0]
  have hs2large : (shellSpacing u) ^ 2 ≥ 390 ^ 2 := by
    nlinarith [sq_nonneg (shellSpacing u - 390)]
  have hs4gap : (shellSpacing u) ^ 4 - (shellSpacing u) ^ 2 ≥ 31 := by
    nlinarith [sq_nonneg ((shellSpacing u) ^ 2 - 2)]
  have hs2u : (shellSpacing u) ^ 2 ≤ (u : ℝ) - 31 := by
    rw [← hs4]
    linarith [hs4gap]
  have hstrictPred : (i - 1 : ℝ) * shellSpacing u <
      r - shellSpacing u / 12 - 1 := by
    have hlarge : 0 < shellSpacing u * (11 / 12 : ℝ) - 2 := by
      nlinarith [hs390]
    have hbase : (i : ℝ) * shellSpacing u - 1 < r := by linarith
    have hgap : (i - 1 : ℝ) * shellSpacing u <
        (i : ℝ) * shellSpacing u - shellSpacing u / 12 - 2 := by
      nlinarith [hlarge]
    linarith
  refine ⟨hs390, ?_, ?_, ?_, hstrictPred⟩
  · have : 2 * shellSpacing u - 1 ≤ r := by
      nlinarith [hfloorLT, hi2R, hs0]
    simpa [r] using this
  · have : r ≤ (shellSpacing u) ^ 2 := hfloorLE.trans hirange
    simpa [r] using this
  · have : r ≤ (u : ℝ) - 31 := hfloorLE.trans (hirange.trans hs2u)
    simpa [r] using this

end AKLT.W.WIN031
