module
public import AKLT.W.H1C021.Basic
public import AKLT.W.H1C021.Basis
public import AKLT.W.H1M047.Main

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

namespace AKLT.W.H1C021

def rationalComplexValue (z : ℚ × ℚ) : ℂ := (z.1 : ℂ) + (z.2 : ℂ) * Complex.I

theorem rationalComplexValue_mul (z w : ℚ × ℚ) :
    rationalComplexValue (ratComplexMul z w) = rationalComplexValue z * rationalComplexValue w := by
  unfold rationalComplexValue ratComplexMul
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem rationalPauli_value (a : Fin 4) (i j : Fin 2) :
    rationalComplexValue (rationalPauli a i j) = pauli a i j := by
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    norm_num [rationalComplexValue, rationalPauli, pauli]

theorem rationalComplexValue_foldl (zs : List (ℚ × ℚ)) (z : ℚ × ℚ) :
    rationalComplexValue (zs.foldl ratComplexMul z) =
      rationalComplexValue z * (zs.map rationalComplexValue).prod := by
  induction zs generalizing z with
  | nil => simp
  | cons w zs ih =>
    simp only [List.foldl_cons, ih, rationalComplexValue_mul, List.map_cons, List.prod_cons]
    ring

theorem rationalOperatorEntry_complex_re (J : Finset (Fin 20))
    (p : VectorPolynomial) (σ τ : J → Fin 2) :
    (rationalOperatorEntry J p σ τ : ℝ) = (pauliOperator J p σ τ).re := by
  classical
  unfold rationalOperatorEntry pauliOperator
  simp only [Rat.cast_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro a _
  let zs := (Finset.univ : Finset J).toList.map (fun j => rationalPauli (a j) (σ j) (τ j))
  have hz : rationalComplexValue (zs.foldl ratComplexMul (1,0)) =
      ∏ j : J, pauli (a j) (σ j) (τ j) := by
    rw [rationalComplexValue_foldl]
    simp only [rationalComplexValue, Rat.cast_one, Rat.cast_zero, zero_mul, add_zero, one_mul]
    simp only [zs, List.map_map, Function.comp_def, rationalPauli_value]
    rw [← List.prod_toFinset _ (Finset.nodup_toList _), Finset.toList_toFinset]
  have hr := congrArg Complex.re hz
  simp only [rationalComplexValue, Complex.add_re, Complex.mul_re, Complex.ratCast_re,
    Complex.ratCast_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero] at hr
  simp only [Rat.cast_mul, Complex.mul_re, Complex.ratCast_re, Complex.ratCast_im,
    zero_mul, sub_zero]
  rw [← hr]

theorem rationalSectorEntry_complex_re (π : PatternData) (r : Representation)
    (ε : ExchangeSigns π) (p : VectorPolynomial) (a b : CentralBasis π r ε) :
    (rationalSectorEntry π r ε p a b : ℝ) =
      (∑ σ, ∑ τ, (exchangeBasisVector π r ε a.val σ : ℂ) *
        pauliOperator (reductionVectors π r) p σ τ *
          (exchangeBasisVector π r ε b.val τ : ℂ)).re := by
  classical
  unfold rationalSectorEntry
  simp only [Rat.cast_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro τ _
  rw [Rat.cast_mul, Rat.cast_mul, rationalOperatorEntry_complex_re]
  simp [Complex.mul_re, Complex.mul_im]

theorem pauliOperator_monomial (J : Finset (Fin 20)) (d : J → Fin 4) (c : ℚ)
    (σ τ : J → Fin 2) :
    pauliOperator J (MvPolynomial.monomial (pauliExponent J d) c) σ τ =
      (c : ℂ) * ∏ j : J, pauli (d j) (σ j) (τ j) := by
  classical
  simp only [pauliOperator, MvPolynomial.coeff_monomial,
    (AKLT.W.H1M047.pauliExponent_injective J).eq_iff]
  simp [apply_ite]

/-- A single Pauli monomial has the product of the literal local integer
congruence forms. This exposes the remaining color/exponent indexing step. -/
theorem rationalSectorEntry_pauliMonomial (π : PatternData) (r : Representation)
    (ε : ExchangeSigns π) (a b : CentralBasis π r ε)
    (d : reductionVectors π r → Fin 4) :
    (rationalSectorEntry π r ε
      (MvPolynomial.monomial (pauliExponent (reductionVectors π r) d) 1) a b : ℝ) =
      (∏ x : reductionGroups π, ∑ s : GroupSlot π r x → Fin 2,
        ∑ t : GroupSlot π r x → Fin 2,
          (groupBasisCoeff π r ε a.val x s : ℂ) *
            (∏ k, pauli (d (groupSlotToken π r x k)) (s k) (t k)) *
              (groupBasisCoeff π r ε b.val x t : ℂ)).re := by
  classical
  rw [rationalSectorEntry_complex_re]
  simp only [pauliOperator_monomial, Rat.cast_one, one_mul]
  rw [sectorTensor_congruence π r ε a.val b.val (fun j => pauli (d j))]

end AKLT.W.H1C021
