import AKLT.W.H1C002.Algebra
import AKLT.W.H1C002.Structure

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs

namespace AKLT.W.H1C002

/-- The reconstructed threshold form has exactly the scale `15 D₀ q`. -/
theorem main : AKLT.Cert.H1.Production.TopLeaves.thresholdScale := by
  intro π hπ r I hI D₀ hD p q hp hq hpq ε a b
  let cur := rationalSectorEntry π r ε
    (invertPolynomial I (reducedPolynomial π r false)) a b
  let nxt := rationalSectorEntry π r ε
    (invertPolynomial I (reducedPolynomial π r true)) a b
  have hcur := integerSectorMatrix_exact π r I D₀ hD ε false a b
  have hnxt := integerSectorMatrix_exact π r I D₀ hD ε true a b
  change (integerSectorMatrix π r ε I D₀ false a b : ℚ) =
    3 * (D₀ : ℚ) * cur at hcur
  change (integerSectorMatrix π r ε I D₀ true a b : ℚ) =
    5 * (D₀ : ℚ) * nxt at hnxt
  have hdiff := rationalSectorEntry_difference π r I ε ((p : ℚ) / q) a b
  have hscale :
      5 * (q : ℚ) * (3 * (D₀ : ℚ) * cur) -
        3 * (p : ℚ) * (5 * (D₀ : ℚ) * nxt) =
      15 * (D₀ : ℚ) * q * (cur - ((p : ℚ) / q) * nxt) := by
    have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
    field_simp [hq0]
    ring
  have hthreshold :
      (thresholdSectorMatrix π r ε I D₀ p q a b : ℚ) =
        5 * (q : ℚ) * (3 * (D₀ : ℚ) * cur) -
          3 * (p : ℚ) * (5 * (D₀ : ℚ) * nxt) := by
    change (((5 * (q : ℤ)) * integerSectorMatrix π r ε I D₀ false a b -
      (3 * (p : ℤ)) * integerSectorMatrix π r ε I D₀ true a b : ℤ) : ℚ) = _
    push_cast
    rw [hcur, hnxt]
  have hcomplex := complexSectorMatrix_exact π r ε _
    (invertedDifference_real π hπ r I ((p : ℚ) / q)) a b
  have hratdiff :
      rationalSectorEntry π r ε
        (invertPolynomial I (reducedDifference π r ((p : ℚ) / q))) a b =
        cur - ((p : ℚ) / q) * nxt := by
    simpa [cur, nxt] using hdiff
  calc
    (thresholdSectorMatrix π r ε I D₀ p q a b : ℂ) =
        (((thresholdSectorMatrix π r ε I D₀ p q a b : ℚ) : ℂ)) := by
          norm_cast
    _ = ((15 * (D₀ : ℚ) * q * (cur - ((p : ℚ) / q) * nxt) : ℚ) : ℂ) := by
          rw [hthreshold, hscale]
    _ = (15 * (D₀ : ℂ) * q) *
        complexSectorMatrix π r ε
          (invertPolynomial I (reducedDifference π r ((p : ℚ) / q))) a b := by
          rw [hcomplex, hratdiff]
          push_cast
          field_simp

end AKLT.W.H1C002

#print axioms AKLT.W.H1C002.main
