module
public import AKLT.Blueprint.Win.NodesShell

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open AKLT.Defs

namespace AKLT.W.WIN004

theorem main : AKLT.Blueprint.Win.RadiusGapStatement := by
  intro u hs i j hij
  let s : ℝ := shellSpacing u
  have hs16 : 16 ≤ s := hs
  have hs_nonneg : 0 ≤ s := by linarith
  have hfloor : (2 * s / 3) < (⌊s⌋ : ℝ) := by
    have hsub : s - 1 < ((⌊s⌋ : ℤ) : ℝ) := Int.sub_one_lt_floor s
    exact (by linarith [hs16] : 2 * s / 3 < s - 1).trans hsub
  have hstep : (i : ℝ) + 1 ≤ (j : ℝ) := by
    have hz : i + 1 ≤ j := by omega
    exact_mod_cast hz
  have hscaled : (i : ℝ) * s + s ≤ (j : ℝ) * s := by
    calc
      (i : ℝ) * s + s = ((i : ℝ) + 1) * s := by ring
      _ ≤ (j : ℝ) * s := mul_le_mul_of_nonneg_right hstep hs_nonneg
  have hfloorGap : ⌊(i : ℝ) * s⌋ + ⌊s⌋ ≤ ⌊(j : ℝ) * s⌋ := by
    exact (Int.le_floor_add ((i : ℝ) * s) s).trans (Int.floor_mono hscaled)
  have hfloorGap' : (⌊s⌋ : ℝ) ≤ (⌊(j : ℝ) * s⌋ : ℝ) - (⌊(i : ℝ) * s⌋ : ℝ) := by
    have hz : ⌊s⌋ ≤ ⌊(j : ℝ) * s⌋ - ⌊(i : ℝ) * s⌋ := by omega
    exact_mod_cast hz
  simp only [shellRadius]
  exact lt_of_lt_of_le hfloor hfloorGap'

end AKLT.W.WIN004
