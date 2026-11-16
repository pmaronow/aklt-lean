import AKLT.W.H1C003.Algebra

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.H1C003

private def ratToComplex (z : ℚ × ℚ) : ℂ := (z.1 : ℂ) + (z.2 : ℂ) * Complex.I

private theorem ratToComplex_mul (z w : ℚ × ℚ) :
    ratToComplex (ratComplexMul z w) = ratToComplex z * ratToComplex w := by
  apply Complex.ext <;>
    simp [ratToComplex, ratComplexMul, Complex.mul_re, Complex.mul_im]

private theorem ratToComplex_pauli (a : Fin 4) (i j : Fin 2) :
    ratToComplex (rationalPauli a i j) = pauli a i j := by
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    simp [ratToComplex, rationalPauli, pauli]

private theorem ratToComplex_foldl (l : List (ℚ × ℚ)) (z : ℚ × ℚ) :
    ratToComplex (l.foldl ratComplexMul z) = ratToComplex z * (l.map ratToComplex).prod := by
  induction l generalizing z with
  | nil => simp
  | cons w l ih =>
      rw [List.foldl_cons, ih, ratToComplex_mul]
      simp only [List.map_cons, List.prod_cons, mul_assoc]

private theorem rationalPauli_product (J : Finset (Fin 20)) (a : J → Fin 4)
    (σ τ : J → Fin 2) :
    ratToComplex (((Finset.univ : Finset J).toList.map
      (fun j => rationalPauli (a j) (σ j) (τ j))).foldl ratComplexMul (1, 0)) =
        ∏ j : J, pauli (a j) (σ j) (τ j) := by
  rw [ratToComplex_foldl]
  simp only [List.map_map, Function.comp_def, ratToComplex_pauli]
  rw [Finset.prod_map_toList]
  simp [ratToComplex]

theorem rationalOperatorEntry_re (J : Finset (Fin 20))
    (p : MvPolynomial (Fin 20 × Fin 3) ℚ) (σ τ : J → Fin 2) :
    (rationalOperatorEntry J p σ τ : ℝ) = (pauliOperator J p σ τ).re := by
  classical
  unfold rationalOperatorEntry pauliOperator
  rw [Complex.re_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro a _
  have hprod := congrArg Complex.re (rationalPauli_product J a σ τ)
  simp only [ratToComplex, Complex.add_re, Complex.ratCast_re, Complex.mul_re,
    Complex.I_re, Complex.ratCast_im, Complex.I_im, mul_zero, zero_mul, sub_self,
    add_zero] at hprod
  rw [hprod]
  simp

private def IntegralPair (z : ℚ × ℚ) : Prop := IntegralRat z.1 ∧ IntegralRat z.2

private theorem integral_zero : IntegralRat 0 := by simpa using integralRat_intCast 0
private theorem integral_one : IntegralRat 1 := by simpa using integralRat_intCast 1
private theorem integral_neg_one : IntegralRat (-1) := by simpa using integralRat_intCast (-1)

private theorem IntegralPair.mul {z w : ℚ × ℚ} (hz : IntegralPair z)
    (hw : IntegralPair w) : IntegralPair (ratComplexMul z w) :=
  ⟨(hz.1.mul hw.1).sub (hz.2.mul hw.2), (hz.1.mul hw.2).add (hz.2.mul hw.1)⟩

private theorem rationalPauli_integral (a : Fin 4) (i j : Fin 2) :
    IntegralPair (rationalPauli a i j) := by
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    simp [rationalPauli, IntegralPair, integral_zero, integral_one, integral_neg_one]

private theorem integral_foldl (l : List (ℚ × ℚ))
    (hl : ∀ z ∈ l, IntegralPair z) (z : ℚ × ℚ) (hz : IntegralPair z) :
    IntegralPair (l.foldl ratComplexMul z) := by
  induction l generalizing z with
  | nil => exact hz
  | cons w l ih =>
      rw [List.foldl_cons]
      exact ih (fun v hv => hl v (List.mem_cons_of_mem w hv)) _
        (hz.mul (hl w List.mem_cons_self))

private theorem rationalPauli_product_integral (J : Finset (Fin 20)) (a : J → Fin 4)
    (σ τ : J → Fin 2) :
    IntegralPair (((Finset.univ : Finset J).toList.map
      (fun j => rationalPauli (a j) (σ j) (τ j))).foldl ratComplexMul (1, 0)) := by
  apply integral_foldl
  · intro z hz
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hz
    exact rationalPauli_integral _ _ _
  · exact ⟨integral_one, integral_zero⟩

theorem scaled_rationalOperatorEntry_integral (J : Finset (Fin 20))
    (p : MvPolynomial (Fin 20 × Fin 3) ℚ) (k : ℚ)
    (hk : ∀ d, IntegralRat (k * p.coeff d)) (σ τ : J → Fin 2) :
    IntegralRat (k * rationalOperatorEntry J p σ τ) := by
  unfold rationalOperatorEntry
  rw [Finset.mul_sum]
  apply integralRat_sum
  intro a _
  rw [← mul_assoc]
  exact (hk _).mul (rationalPauli_product_integral J a σ τ).1

theorem scaled_rationalSectorEntry_integral (π : PatternData) (r : Representation)
    (ε : ExchangeSigns π) (p : MvPolynomial (Fin 20 × Fin 3) ℚ) (k : ℚ)
    (hk : ∀ d, IntegralRat (k * p.coeff d)) (a b : CentralBasis π r ε) :
    IntegralRat (k * rationalSectorEntry π r ε p a b) := by
  unfold rationalSectorEntry
  rw [Finset.mul_sum]
  apply integralRat_sum
  intro σ _
  rw [Finset.mul_sum]
  apply integralRat_sum
  intro τ _
  have h := ((integralRat_intCast (exchangeBasisVector π r ε a.val σ)).mul
    (scaled_rationalOperatorEntry_integral _ p k hk σ τ)).mul
      (integralRat_intCast (exchangeBasisVector π r ε b.val τ))
  convert h using 1
  ring

theorem integerSectorMatrix_cast (π : PatternData) (r : Representation)
    (ε : ExchangeSigns π) (I : Finset (Fin 20)) (D₀ : ℕ)
    (hD : ClearsDenominator π r D₀) (next : Bool) (a b : CentralBasis π r ε) :
    (integerSectorMatrix π r ε I D₀ next a b : ℚ) =
      (if next then 5 else 3) * (D₀ : ℚ) *
        rationalSectorEntry π r ε (invertPolynomial I (reducedPolynomial π r next)) a b := by
  obtain ⟨z, hz⟩ := scaled_rationalSectorEntry_integral π r ε
    (invertPolynomial I (reducedPolynomial π r next)) ((if next then 5 else 3) * (D₀ : ℚ))
    (denominator_inverted_coeff π r D₀ hD I next) a b
  change (⌊_⌋ : ℚ) = _
  rw [hz, Int.floor_intCast]

end AKLT.W.H1C003
