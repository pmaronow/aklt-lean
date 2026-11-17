module
public import AKLT.Blueprint.Rec.NodesLogMean
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC027

theorem main : AKLT.Blueprint.Rec.LogEnclosureLowerStatement := by
  intro s hs0 hs1
  let x : ℝ := s
  have hx0 : 0 < x := by
    change (0 : ℝ) < (s : ℝ)
    exact_mod_cast hs0
  have hx1 : x < 1 := by
    change (s : ℝ) < 1
    exact_mod_cast hs1
  let t : ℝ := (1 - x) / (1 + x)
  have ht0 : 0 < t := by
    dsimp [t]
    exact div_pos (by linarith) (by linarith)
  have ht1 : t < 1 := by
    dsimp [t]
    rw [div_lt_one (by linarith)]
    linarith
  let a : ℝ := 2 * t / (1 - t)
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos (by positivity) (by linarith)
  have htden : 1 - t ≠ 0 := ne_of_gt (by linarith : 0 < 1 - t)
  have hden : a + 2 = 2 / (1 - t) := by
    dsimp [a]
    field_simp [htden]
    ; ring
  have hparam : a / (a + 2) = t := by
    rw [hden]
    dsimp [a]
    field_simp [htden]
  have harg : 1 + a = (1 + t) / (1 - t) := by
    dsimp [a]
    field_simp [htden]
    ; ring
  have hseries0 := Real.hasSum_log_one_add ha.le
  have hseries : HasSum (fun k : ℕ => (2 : ℝ) * t ^ (2 * k + 1) / (2 * k + 1 : ℝ))
      (Real.log ((1 + t) / (1 - t))) := by
    convert hseries0 using 1
    · funext k
      rw [hparam]
      ring
    · rw [harg]
  have hpartial :
      (∑ k ∈ Finset.range 8, (2 : ℝ) * t ^ (2 * k + 1) / (2 * k + 1 : ℝ)) ≤
        Real.log ((1 + t) / (1 - t)) := by
    calc
      _ ≤ ∑' k : ℕ, (2 : ℝ) * t ^ (2 * k + 1) / (2 * k + 1 : ℝ) :=
        hseries.summable.sum_le_tsum _ (by
          intro k hk
          positivity)
      _ = Real.log ((1 + t) / (1 - t)) := hseries.tsum_eq
  have hpartial' :
      2 * (∑ k ∈ Finset.range 8, t ^ (2 * k + 1) / (2 * k + 1 : ℝ)) ≤
        Real.log ((1 + t) / (1 - t)) := by
    convert hpartial using 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hlog : -Real.log x = Real.log ((1 + t) / (1 - t)) := by
    rw [← Real.log_inv x]
    congr 1
    dsimp [t]
    field_simp [hx0.ne']
    ; ring
  have hlow :
      (2 / (1 - x)) * (∑ k ∈ Finset.range 8, t ^ (2 * k + 1) / (2 * k + 1 : ℝ)) ≤
        (-Real.log x) / (1 - x) := by
    rw [hlog]
    calc
      (2 / (1 - x)) * (∑ k ∈ Finset.range 8, t ^ (2 * k + 1) / (2 * k + 1 : ℝ)) =
          (1 / (1 - x)) *
            (2 * (∑ k ∈ Finset.range 8, t ^ (2 * k + 1) / (2 * k + 1 : ℝ))) := by ring
      _ ≤ (1 / (1 - x)) * Real.log ((1 + t) / (1 - t)) :=
        mul_le_mul_of_nonneg_left hpartial' (by positivity)
      _ = Real.log ((1 + t) / (1 - t)) / (1 - x) := by ring
  have hlogne : Real.log x ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hx0 (ne_of_lt hx1)
  have hmean : logarithmicMean x 1 = (1 - x) / (-Real.log x) := by
    simp [logarithmicMean, ne_of_lt hx1, Real.log_one]
    field_simp [hlogne]
    ; ring
  have hrecip : reciprocalLogMean x = (-Real.log x) / (1 - x) := by
    rw [reciprocalLogMean, hmean]
    field_simp [hlogne, ne_of_gt (show 0 < 1 - x by linarith)]
  have htarget :
      (logMeanLower s : ℝ) =
        (2 / (1 - x)) * (∑ k ∈ Finset.range 8,
          t ^ (2 * k + 1) / (2 * k + 1 : ℝ)) := by
    simp only [logMeanLower, x]
    push_cast
    have hqt : (1 - (s : ℝ)) / (1 + (s : ℝ)) = t := by
      dsimp [t, x]
    rw [hqt]
  rw [htarget, hrecip]
  exact hlow

end AKLT.W.REC027
