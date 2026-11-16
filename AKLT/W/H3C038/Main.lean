import CertData.H3.Bridge.Interface

namespace AKLT.W.H3C038

open CertData.H3.Bridge
open AKLT.Cert.H3.Production

private theorem numericScale : NumericScaleLeaf := by
  intro E hE r
  unfold resultValue finalNumerator finalDenominator
  push_cast
  have hK : (E.denominator : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hE)
  field_simp [hK]

theorem main : CertData.H3.Bridge.RationalCeilingLeaf := by
  intro E hE r c hcheck
  have hscale := numericScale E hE r
  have hcheck' : r.ok = true ∧ 10^9 * finalNumerator E r ≤ c * finalDenominator E := by
    simpa [ceilingCheck, Bool.and_eq_true, decide_eq_true_eq] using hcheck
  have hnat := hcheck'.2
  have hrat : (10^9 : ℚ) * (finalNumerator E r : ℚ) ≤
      (c : ℚ) * (finalDenominator E : ℚ) := by
    exact_mod_cast hnat
  have hden : (0 : ℚ) < (finalDenominator E : ℚ) := by
    unfold finalDenominator
    positivity
  rw [hscale]
  calc
    (10^9 : ℚ) * ((finalNumerator E r : ℚ) / (finalDenominator E : ℚ)) =
        ((10^9 : ℚ) * (finalNumerator E r : ℚ)) / (finalDenominator E : ℚ) := by ring
    _ ≤ (c : ℚ) := (div_le_iff₀ hden).2 hrat

#print axioms main

end AKLT.W.H3C038
