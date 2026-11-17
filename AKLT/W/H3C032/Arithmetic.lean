module
public import CertData.H3.Bridge.Interface

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H3C032

open AKLT.Cert.H3.Production AKLT.Defs

/-- The rational score after normalizing both stored numerators by the same scale. -/
def scaledScore (K X A : Nat) : ℚ :=
  ((X : ℚ) / K - 1) / (((X : ℚ) / K) * ((A : ℚ) / K))

private theorem scaledScore_eq (K X A : Nat) (hK : 0 < K) (hX : K ≤ X)
    (hA : 0 < A) :
    scaledScore K X A = ((X - K : Nat) : ℚ) * K / ((X : ℚ) * A) := by
  have hKq : (K : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hK)
  have hXq : (X : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le hK hX))
  have hAq : (A : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hA)
  rw [Nat.cast_sub hX]
  unfold scaledScore
  field_simp

/-- Exact natural cross-products compare the normalized scores, including equality. -/
theorem scaledScore_comparison (K X Y A B : Nat) (hK : 0 < K)
    (hX : K ≤ X) (hY : K ≤ Y) (hA : 0 < A) (hB : 0 < B) :
    (scaledScore K X A < scaledScore K Y B ↔
      (X - K) * Y * B < (Y - K) * X * A) ∧
    (scaledScore K X A = scaledScore K Y B ↔
      (X - K) * Y * B = (Y - K) * X * A) := by
  have hKq : (0 : ℚ) < K := by exact_mod_cast hK
  have hXq : (0 : ℚ) < X := by exact_mod_cast (lt_of_lt_of_le hK hX)
  have hYq : (0 : ℚ) < Y := by exact_mod_cast (lt_of_lt_of_le hK hY)
  have hAq : (0 : ℚ) < A := by exact_mod_cast hA
  have hBq : (0 : ℚ) < B := by exact_mod_cast hB
  rw [scaledScore_eq K X A hK hX hA, scaledScore_eq K Y B hK hY hB]
  have hl : ((X - K : Nat) : ℚ) * K * ((Y : ℚ) * B) =
      K * (((X - K) * Y * B : Nat) : ℚ) := by push_cast; ring
  have hr : ((Y - K : Nat) : ℚ) * K * ((X : ℚ) * A) =
      K * (((Y - K) * X * A : Nat) : ℚ) := by push_cast; ring
  constructor
  · rw [div_lt_div_iff₀ (mul_pos hXq hAq) (mul_pos hYq hBq), hl, hr,
      mul_lt_mul_iff_right₀ hKq]
    exact_mod_cast Iff.rfl
  · rw [div_eq_div_iff (ne_of_gt (mul_pos hXq hAq)) (ne_of_gt (mul_pos hYq hBq)),
      hl, hr, mul_right_inj' (ne_of_gt hKq)]
    exact_mod_cast Iff.rfl

theorem exposureFactor_normalized (E : Exact) (hE : CertData.H3.Bridge.ExactValid E)
    (a : RewardItem) :
    (exposureFactor E a : ℚ) / E.denominator = passageFactor a.straight := by
  cases h : a.straight
  · simp only [exposureFactor, h, Bool.false_eq_true, ↓reduceIte, Nat.cast_mul,
      Nat.cast_ofNat]
    calc
      (E.turn : ℚ) * 3 / E.denominator = ((E.turn : ℚ) / E.denominator) * 3 := by ring
      _ = passageFactor false := by rw [hE.2.2.1]; ring
  · simp only [exposureFactor, h, ↓reduceIte, Nat.cast_mul, Nat.cast_ofNat]
    calc
      (E.straight : ℚ) * 3 / E.denominator =
          ((E.straight : ℚ) / E.denominator) * 3 := by ring
      _ = passageFactor true := by rw [hE.2.1]; ring

theorem denominator_le_exposureFactor (E : Exact)
    (hE : CertData.H3.Bridge.ExactValid E) (a : RewardItem) :
    E.denominator ≤ exposureFactor E a := by
  have hKq : (0 : ℚ) < E.denominator := by exact_mod_cast hE.1
  have hf : (1 : ℚ) ≤ (exposureFactor E a : ℚ) / E.denominator := by
    rw [exposureFactor_normalized E hE a]
    cases a.straight <;> norm_num [passageFactor, localThreshold]
  have hx : (E.denominator : ℚ) ≤ exposureFactor E a := by
    simpa only [one_mul] using (le_div_iff₀ hKq).mp hf
  exact_mod_cast hx

end AKLT.W.H3C032
