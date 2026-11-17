module
public import AKLT.Blueprint.Rec.NodesLocal
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section

namespace AKLT.W.REC035

open AKLT.Defs

private lemma exp_secant_mono {a b u v : ℝ} (hab : a < b)
    (hau : a ≤ u) (hbv : b ≤ v) (huv : u < v) :
    (Real.exp b - Real.exp a) / (b - a) ≤
      (Real.exp v - Real.exp u) / (v - u) := by
  by_cases hub : u < b
  · have hleft : (Real.exp b - Real.exp a) / (b - a) ≤
        (Real.exp b - Real.exp u) / (b - u) := by
      by_cases hau' : a = u
      · subst u
        exact le_of_eq rfl
      · have h := convexOn_exp.secant_mono
          (a := b) (x := a) (y := u) (by simp) (by simp) (by simp)
          (ne_of_lt hab) (ne_of_lt hub) hau
        have h₁ : (Real.exp b - Real.exp a) / (b - a) =
            (Real.exp a - Real.exp b) / (a - b) := by
          simpa [neg_sub] using
            (neg_div_neg_eq (Real.exp b - Real.exp a) (b - a)).symm
        have h₂ : (Real.exp b - Real.exp u) / (b - u) =
            (Real.exp u - Real.exp b) / (u - b) := by
          simpa [neg_sub] using
            (neg_div_neg_eq (Real.exp b - Real.exp u) (b - u)).symm
        rw [h₁, h₂]
        exact h
    have hright : (Real.exp b - Real.exp u) / (b - u) ≤
        (Real.exp v - Real.exp u) / (v - u) := by
      by_cases hbv' : b = v
      · subst v
        exact le_of_eq rfl
      · have h := convexOn_exp.secant_mono
          (a := u) (x := b) (y := v) (by simp) (by simp) (by simp)
          (ne_of_gt hub) (ne_of_gt (lt_of_lt_of_le hub hbv)) hbv
        exact h
    exact hleft.trans hright
  · have hbu : b ≤ u := le_of_not_gt hub
    have hmid : (Real.exp b - Real.exp a) / (b - a) ≤
        (Real.exp u - Real.exp a) / (u - a) := by
      by_cases hEq : b = u
      · subst u
        exact le_of_eq rfl
      · have h := convexOn_exp.secant_mono
          (a := a) (x := b) (y := u) (by simp) (by simp) (by simp)
          (ne_of_gt hab) (ne_of_gt (lt_of_lt_of_le hab hbu)) hbu
        exact h
    have hright : (Real.exp u - Real.exp a) / (u - a) ≤
        (Real.exp v - Real.exp u) / (v - u) :=
      convexOn_exp.slope_mono_adjacent (by simp) (by simp)
        (lt_of_lt_of_le hab hbu) huv
    exact hmid.trans hright

private lemma logMean_eq_exp_secant {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxy : Real.log x < Real.log y) :
    logarithmicMean x y =
      (Real.exp (Real.log y) - Real.exp (Real.log x)) /
        (Real.log y - Real.log x) := by
  have hne : x ≠ y := by
    intro he
    subst y
    exact (lt_irrefl _ hxy)
  unfold logarithmicMean
  rw [if_neg hne, Real.exp_log hx, Real.exp_log hy]
  have hdiv : (x - y) / (Real.log x - Real.log y) =
      (y - x) / (Real.log y - Real.log x) := by
    simpa [neg_sub] using
      (neg_div_neg_eq (x - y) (Real.log x - Real.log y)).symm
  exact hdiv

private lemma logMean_comm (x y : ℝ) : logarithmicMean x y = logarithmicMean y x := by
  by_cases h : x = y
  · subst y
    rfl
  · simp only [logarithmicMean, if_neg h, if_neg (Ne.symm h)]
    simpa [neg_sub] using
      (neg_div_neg_eq (x - y) (Real.log x - Real.log y)).symm

private lemma logMean_le_one {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    logarithmicMean s 1 ≤ 1 := by
  have hlog : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hs
  have hlogneg : Real.log s < 0 := by
    have := Real.log_lt_log hs hs1
    simpa using this
  have hden : 0 < -Real.log s := by linarith
  have hnumer : 1 - s ≤ -Real.log s := by linarith
  have hfrac : (1 - s) / (-Real.log s) ≤ 1 := (div_le_one hden).2 hnumer
  have hne : s ≠ 1 := ne_of_lt hs1
  rw [logarithmicMean, if_neg hne, Real.log_one, sub_zero]
  have heq : (s - 1) / Real.log s = (1 - s) / (-Real.log s) := by
    simpa [neg_sub] using (neg_div_neg_eq (s - 1) (Real.log s)).symm
  rw [heq]
  exact hfrac

private lemma logMean_lower_bound {s x y : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (hx : 0 < x) (hy : 0 < y) (hsx : s ≤ x) (hone : 1 ≤ y) :
    logarithmicMean s 1 ≤ logarithmicMean x y := by
  have hbase : Real.log s < 0 := by
    have := Real.log_lt_log hs hs1
    simpa using this
  have hbaseId := logMean_eq_exp_secant hs zero_lt_one
    (by simpa using hbase)
  by_cases hxy : x = y
  · subst y
    have hxone : 1 ≤ x := by simpa using hone
    have htarget : logarithmicMean x x = x := by simp [logarithmicMean]
    rw [htarget]
    exact (logMean_le_one hs hs1).trans hxone
  · have hlogne : Real.log x ≠ Real.log y := by
      intro hlog
      apply hxy
      apply le_antisymm
      · exact (Real.log_le_log_iff hx hy).mp hlog.le
      · exact (Real.log_le_log_iff hy hx).mp hlog.ge
    by_cases horder : Real.log x < Real.log y
    · have htarget := logMean_eq_exp_secant hx hy horder
      have hleft : Real.log s ≤ Real.log x := Real.log_le_log hs hsx
      have hright : Real.log 1 ≤ Real.log y := Real.log_le_log one_pos hone
      rw [hbaseId, htarget]
      exact exp_secant_mono (by simpa using hbase) hleft hright horder
    · have horder' : Real.log y < Real.log x :=
        lt_of_le_of_ne (le_of_not_gt horder) hlogne.symm
      have htarget := logMean_eq_exp_secant hy hx horder'
      have hleft : Real.log s ≤ Real.log y := by
        have hsone : s ≤ 1 := le_of_lt hs1
        exact Real.log_le_log hs (le_trans hsone hone)
      have hright : Real.log 1 ≤ Real.log x := by
        have h1x : (1 : ℝ) ≤ x := le_trans hone (le_of_lt (by
          exact (Real.log_lt_log_iff hy hx).mp horder'))
        exact Real.log_le_log one_pos h1x
      rw [hbaseId, logMean_comm x y, htarget]
      exact exp_secant_mono (by simpa using hbase) hleft hright horder'

theorem main : AKLT.Blueprint.Rec.BetaAnalyticStatement := by
  intro c It I₀ Jt J₀ hc₀ hc₁ hIt hI₀ hJt hJ₀
  let s : ℝ := (116 / 125) * c
  have hcpos : 0 < c := by linarith
  have hspos : 0 < s := by dsimp [s]; positivity
  have hslt : s < 1 := by dsimp [s]; nlinarith
  have hItlower : s ≤ It := by
    dsimp [s]
    calc
      (116 / 125 : ℝ) * c = c * (116 / 125) := by ring
      _ ≤ c * Jt := mul_le_mul_of_nonneg_left hJt (le_of_lt hcpos)
      _ ≤ It := hIt
  have hI₀lower : 1 ≤ I₀ := hJ₀.trans hI₀
  have hItpos : 0 < It := lt_of_lt_of_le hspos hItlower
  have hI₀pos : 0 < I₀ := lt_of_lt_of_le zero_lt_one hI₀lower
  have hmean : logarithmicMean s 1 ≤ logarithmicMean It I₀ :=
    logMean_lower_bound hspos hslt hItpos hI₀pos hItlower hI₀lower
  have hmeanpos : 0 < logarithmicMean s 1 := by
    have hlogneg : Real.log s < 0 := by
      have := Real.log_lt_log hspos hslt
      simpa using this
    rw [logarithmicMean, if_neg (ne_of_lt hslt), Real.log_one, sub_zero]
    exact (div_pos_iff).2 (Or.inr ⟨by linarith, hlogneg⟩)
  have hinv : (logarithmicMean It I₀)⁻¹ ≤ (logarithmicMean s 1)⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hmeanpos hmean
  rw [show reciprocalLogMean s = 1 / logarithmicMean s 1 by
    simp [reciprocalLogMean, div_eq_mul_inv]]
  have hscaled : (1 / 3 : ℝ) * (logarithmicMean It I₀)⁻¹ ≤
      (1 / 3 : ℝ) * (logarithmicMean s 1)⁻¹ :=
    mul_le_mul_of_nonneg_left hinv (by norm_num)
  simpa [one_div, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hscaled

end AKLT.W.REC035

#print axioms AKLT.W.REC035.main
