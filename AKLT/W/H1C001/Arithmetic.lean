import AKLT.W.H1C001.RationalPauli
import AKLT.W.H1C022.Main

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.H1C001

private def inversionSign (I : Finset (Fin 20)) (v : Fin 20 × Fin 3) : ℤ :=
  if v.1 ∈ I then -1 else 1

private def inversionFactor (I : Finset (Fin 20)) (d : (Fin 20 × Fin 3) →₀ ℕ) : ℤ :=
  d.prod fun v e => inversionSign I v ^ e

private lemma invert_monomial (I : Finset (Fin 20))
    (d : (Fin 20 × Fin 3) →₀ ℕ) (c : ℚ) :
    invertPolynomial I (MvPolynomial.monomial d c) =
      MvPolynomial.monomial d (c * (inversionFactor I d : ℚ)) := by
  have hsign (v : Fin 20 × Fin 3) :
      (if v.1 ∈ I then (-1 : MvPolynomial (Fin 20 × Fin 3) ℚ) else 1) =
        MvPolynomial.C (inversionSign I v : ℚ) := by
    by_cases hv : v.1 ∈ I <;> simp [inversionSign, hv]
  rw [invertPolynomial, MvPolynomial.eval₂Hom_monomial, MvPolynomial.monomial_eq]
  simp_rw [hsign]
  have hprod :
      d.prod (fun v e =>
        (MvPolynomial.C (inversionSign I v : ℚ) * MvPolynomial.X v) ^ e) =
      MvPolynomial.C (inversionFactor I d : ℚ) *
        d.prod (fun v e => MvPolynomial.X v ^ e) := by
    simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, inversionFactor,
      Int.cast_prod, Int.cast_pow, ← map_pow, ← map_prod]
  rw [hprod, ← mul_assoc, ← map_mul]

/-- Inverting variables multiplies every coefficient by an integer sign. -/
theorem invertPolynomial_coeff (I : Finset (Fin 20))
    (p : MvPolynomial (Fin 20 × Fin 3) ℚ) (d : (Fin 20 × Fin 3) →₀ ℕ) :
    ∃ z : ℤ, (invertPolynomial I p).coeff d = p.coeff d * (z : ℚ) := by
  classical
  refine ⟨inversionFactor I d, ?_⟩
  have hinv : invertPolynomial I p =
      ∑ m ∈ p.support, MvPolynomial.monomial m (p.coeff m * (inversionFactor I m : ℚ)) := by
    conv_lhs => rw [MvPolynomial.as_sum p]
    unfold invertPolynomial
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro m _
    exact invert_monomial I m (p.coeff m)
  rw [hinv, MvPolynomial.coeff_sum]
  by_cases hd : d ∈ p.support
  · simp only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq', hd, ite_true]
  · have hz : p.coeff d = 0 := MvPolynomial.notMem_support_iff.mp hd
    simp only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq', hd, ite_false, hz, zero_mul]

/-- Denominator clearing survives the allowed sign substitutions. -/
theorem scaled_inverted_coeff_integral (π : PatternData) (r : Representation)
    (I : Finset (Fin 20)) (D₀ : ℕ) (hD : ClearsDenominator π r D₀)
    (next : Bool) (d : (Fin 20 × Fin 3) →₀ ℕ) :
    (MvPolynomial.C ((if next then 5 else 3) * (D₀ : ℚ)) *
      invertPolynomial I (reducedPolynomial π r next)).coeff d ∈ integerRationals := by
  rw [MvPolynomial.coeff_C_mul]
  obtain ⟨z, hz⟩ := invertPolynomial_coeff I (reducedPolynomial π r next) d
  rw [hz, ← mul_assoc]
  apply integerRationals.mul_mem _ (intCast_mem integerRationals z)
  by_cases hd : d ∈ (reducedPolynomial π r next).support
  · obtain ⟨w, hw⟩ := hD.2 next d hd
    rw [hw]
    exact intCast_mem integerRationals w
  · rw [MvPolynomial.notMem_support_iff.mp hd, mul_zero]
    exact integerRationals.zero_mem

/-- The scaled rational sector form already has integer entries before rounding. -/
theorem scaled_sector_integral (π : PatternData) (r : Representation)
    (I : Finset (Fin 20)) (D₀ : ℕ) (hD : ClearsDenominator π r D₀)
    (ε : ExchangeSigns π) (next : Bool) (a b : CentralBasis π r ε) :
    ∃ z : ℤ, (if next then 5 else 3) * (D₀ : ℚ) * rationalSectorEntry π r ε
      (invertPolynomial I (reducedPolynomial π r next)) a b = z := by
  have h := rationalSectorEntry_integral π r ε
    (MvPolynomial.C ((if next then 5 else 3) * (D₀ : ℚ)) *
      invertPolynomial I (reducedPolynomial π r next))
    (scaled_inverted_coeff_integral π r I D₀ hD next) a b
  rw [AKLT.W.H1C022.main π r ε a b] at h
  obtain ⟨z, hz⟩ := h
  exact ⟨z, hz.symm⟩

#print axioms invertPolynomial_coeff
#print axioms scaled_inverted_coeff_integral
#print axioms scaled_sector_integral

end AKLT.W.H1C001
