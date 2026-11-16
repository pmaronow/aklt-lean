import AKLT.Blueprint.Rec.NodesKernel

noncomputable section
open scoped BigOperators

namespace AKLT.W.REC068

private theorem integer_shift_bound (b θ : ℝ) (hb : 0 < b) (hbt : b < θ)
    (hθ : θ ≤ 1) (n s : ℕ) (hs : s ≤ n + 1) :
    0 ≤ θ ^ (-(s : ℤ)) - 1 ∧
      θ ^ (-(s : ℤ)) - 1 ≤
        (1 - θ) * (n + 1 : ℝ) * b ^ (-(n : ℤ) - 2) := by
  have hθpos : 0 < θ := hb.trans hbt
  have hb1 : b ≤ 1 := hbt.le.trans hθ
  have hden : 0 < θ ^ s := pow_pos hθpos s
  have hdenb : 0 < b ^ (n + 2) := pow_pos hb (n + 2)
  have hden_cmp : b ^ (n + 2) ≤ θ ^ s := by
    calc
      b ^ (n + 2) ≤ b ^ s :=
        pow_le_pow_of_le_one hb.le hb1 (by omega)
      _ ≤ θ ^ s := pow_le_pow_left₀ hb.le hbt.le s
  have hinv_cmp : 1 / θ ^ s ≤ 1 / b ^ (n + 2) :=
    one_div_le_one_div_of_le hdenb hden_cmp
  have hgeom_nonneg : 0 ≤ (∑ i ∈ Finset.range s, θ ^ i) :=
    Finset.sum_nonneg fun i hi => pow_nonneg hθpos.le i
  have hgeom_le : (∑ i ∈ Finset.range s, θ ^ i) ≤ (s : ℝ) := by
    calc
      (∑ i ∈ Finset.range s, θ ^ i) ≤ ∑ i ∈ Finset.range s, (1 : ℝ) :=
        Finset.sum_le_sum fun i hi => pow_le_one₀ hθpos.le hθ
      _ = (s : ℝ) := by simp
  have hzpow : θ ^ (-(s : ℤ)) = 1 / θ ^ s := by
    simp [zpow_neg, zpow_natCast, one_div]
  have hformula : θ ^ (-(s : ℤ)) - 1 =
      (1 - θ) * (∑ i ∈ Finset.range s, θ ^ i) / θ ^ s := by
    rw [hzpow]
    field_simp [ne_of_gt hden]
    rw [mul_neg_geom_sum]
  have hone : 0 ≤ 1 - θ := sub_nonneg.mpr hθ
  have hnum : 0 ≤ (1 - θ) * (∑ i ∈ Finset.range s, θ ^ i) :=
    mul_nonneg hone hgeom_nonneg
  have hnum_le : (1 - θ) * (∑ i ∈ Finset.range s, θ ^ i) ≤
      (1 - θ) * (s : ℝ) :=
    mul_le_mul_of_nonneg_left hgeom_le hone
  have hshift_nonneg : 0 ≤ θ ^ (-(s : ℤ)) - 1 := by
    rw [hformula]
    exact div_nonneg hnum (le_of_lt hden)
  have hshift_le : θ ^ (-(s : ℤ)) - 1 ≤
      ((1 - θ) * (s : ℝ)) * (1 / b ^ (n + 2)) := by
    rw [hformula]
    calc
      ((1 - θ) * (∑ i ∈ Finset.range s, θ ^ i)) / θ ^ s ≤
          ((1 - θ) * (s : ℝ)) / θ ^ s :=
        div_le_div_of_nonneg_right hnum_le hden.le
      _ = ((1 - θ) * (s : ℝ)) * (1 / θ ^ s) := by ring
      _ ≤ ((1 - θ) * (s : ℝ)) * (1 / b ^ (n + 2)) :=
        mul_le_mul_of_nonneg_left hinv_cmp (mul_nonneg hone (Nat.cast_nonneg s))
  have hsreal : (s : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast hs
  have hinv_nonneg : 0 ≤ (1 / b ^ (n + 2) : ℝ) := (div_pos one_pos hdenb).le
  have htargetpow : (1 / b ^ (n + 2) : ℝ) = b ^ (-(n : ℤ) - 2) := by
    have hexp : -(n : ℤ) - 2 = -((n + 2 : ℕ) : ℤ) := by omega
    rw [hexp, zpow_neg, zpow_natCast]
    simp [one_div]
  constructor
  · exact hshift_nonneg
  · calc
      θ ^ (-(s : ℤ)) - 1 ≤
          ((1 - θ) * (s : ℝ)) * (1 / b ^ (n + 2)) := hshift_le
      _ ≤ ((1 - θ) * (n + 1 : ℝ)) * (1 / b ^ (n + 2)) := by
        apply mul_le_mul_of_nonneg_right _ hinv_nonneg
        exact mul_le_mul_of_nonneg_left hsreal hone
      _ = (1 - θ) * (n + 1 : ℝ) * b ^ (-(n : ℤ) - 2) := by rw [htargetpow]

theorem main : AKLT.Blueprint.Rec.ShiftPowerIncrementStatement := by
  intro b θ hb hbt hθ n s hs
  exact integer_shift_bound b θ hb hbt hθ n s hs

end AKLT.W.REC068
