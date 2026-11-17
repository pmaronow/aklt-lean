module
public import AKLT.W.H1C003.Reflection
public import AKLT.W.H1C003.Pauli

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.H1C003

private theorem rationalOperatorEntry_cast (J : Finset (Fin 20))
    (p : MvPolynomial (Fin 20 × Fin 3) ℚ) (σ τ : J → Fin 2)
    (hreal : (pauliOperator J p σ τ).im = 0) :
    (rationalOperatorEntry J p σ τ : ℂ) = pauliOperator J p σ τ := by
  apply Complex.ext
  · simpa only [Complex.ratCast_re] using rationalOperatorEntry_re J p σ τ
  · simpa only [Complex.ratCast_im] using hreal.symm

theorem inverted_rationalSectorEntry_cast (π : PatternData) (hπ : π.Covered)
    (r : Representation) (ε : ExchangeSigns π) (I : Finset (Fin 20))
    (next : Bool) (a b : CentralBasis π r ε) :
    (rationalSectorEntry π r ε (invertPolynomial I (reducedPolynomial π r next)) a b : ℂ) =
      complexSectorMatrix π r ε (invertPolynomial I (reducedPolynomial π r next)) a b := by
  classical
  unfold rationalSectorEntry complexSectorMatrix
  push_cast
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro τ _
  rw [rationalOperatorEntry_cast _ _ σ τ
    (inverted_reducedPolynomial_real π hπ r I _ next σ τ)]

theorem integerSectorMatrix_cast_complex (π : PatternData) (hπ : π.Covered)
    (r : Representation) (ε : ExchangeSigns π) (I : Finset (Fin 20)) (D₀ : ℕ)
    (hD : ClearsDenominator π r D₀) (next : Bool) (a b : CentralBasis π r ε) :
    (integerSectorMatrix π r ε I D₀ next a b : ℂ) =
      (if next then 5 else 3) * (D₀ : ℂ) *
        complexSectorMatrix π r ε (invertPolynomial I (reducedPolynomial π r next)) a b := by
  have h := congrArg (fun x : ℚ => (x : ℂ))
    (integerSectorMatrix_cast π r ε I D₀ hD next a b)
  cases next <;>
    simpa only [Bool.false_eq_true, ite_false, ite_true, Rat.cast_intCast, Rat.cast_mul,
      Rat.cast_ofNat, Rat.cast_natCast,
      inverted_rationalSectorEntry_cast π hπ r ε I] using h

private theorem pauliOperator_sub_C_mul (J : Finset (Fin 20))
    (p q : MvPolynomial (Fin 20 × Fin 3) ℚ) (c : ℚ) (σ τ : J → Fin 2) :
    pauliOperator J (p - MvPolynomial.C c * q) σ τ =
      pauliOperator J p σ τ - (c : ℂ) * pauliOperator J q σ τ := by
  classical
  unfold pauliOperator
  simp only [MvPolynomial.coeff_sub, MvPolynomial.coeff_C_mul, Rat.cast_sub, Rat.cast_mul,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring

private theorem complexSectorMatrix_sub_C_mul (π : PatternData) (r : Representation)
    (ε : ExchangeSigns π) (p q : MvPolynomial (Fin 20 × Fin 3) ℚ) (c : ℚ)
    (a b : CentralBasis π r ε) :
    complexSectorMatrix π r ε (p - MvPolynomial.C c * q) a b =
      complexSectorMatrix π r ε p a b - (c : ℂ) * complexSectorMatrix π r ε q a b := by
  classical
  unfold complexSectorMatrix
  simp only [pauliOperator_sub_C_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro τ _
  ring

private theorem invertPolynomial_difference (π : PatternData) (r : Representation)
    (I : Finset (Fin 20)) (c : ℚ) :
    invertPolynomial I (reducedDifference π r c) =
      invertPolynomial I (reducedPolynomial π r false) -
        MvPolynomial.C c * invertPolynomial I (reducedPolynomial π r true) := by
  simp only [invertPolynomial_eq_scaleVariables, reducedDifference, map_sub, map_mul,
    scaleVariables_C]

/-- Exact reconstruction at the positive scale, with no residual assumptions. -/
theorem thresholdScale_proof : AKLT.Cert.H1.Production.TopLeaves.thresholdScale := by
  intro π hπ r I _ D₀ hD p q _ hq _ ε a b
  have hcur := integerSectorMatrix_cast_complex π hπ r ε I D₀ hD false a b
  have hnext := integerSectorMatrix_cast_complex π hπ r ε I D₀ hD true a b
  simp only [Bool.false_eq_true, ite_false, ite_true] at hcur hnext
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  change (((5 * (q : ℤ)) * integerSectorMatrix π r ε I D₀ false a b -
    (3 * (p : ℤ)) * integerSectorMatrix π r ε I D₀ true a b : ℤ) : ℂ) = _
  push_cast
  rw [hcur, hnext, invertPolynomial_difference, complexSectorMatrix_sub_C_mul]
  push_cast
  field_simp [hqC]
  ring

end AKLT.W.H1C003
