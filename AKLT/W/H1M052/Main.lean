module
public import AKLT.W.H1M052.Raw

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs AKLT.Blueprint.H1

namespace AKLT.W.H1M052

theorem pauliOperator_invert_difference
    (J I : Finset (Fin 20)) (p q : VectorPolynomial) (c : ℚ) :
    pauliOperator J (invertPolynomial I (p - MvPolynomial.C c * q)) =
      pauliOperator J (invertPolynomial I p) -
        (c : ℂ) • pauliOperator J (invertPolynomial I q) := by
  have hpoly : invertPolynomial I (p - MvPolynomial.C c * q) =
      invertPolynomial I p - MvPolynomial.C c * invertPolynomial I q := by
    simp only [invertPolynomial, map_sub, map_mul, MvPolynomial.eval₂Hom_C]
  ext σ τ
  simp only [pauliOperator, hpoly, MvPolynomial.coeff_sub,
    MvPolynomial.coeff_C_mul, Matrix.sub_apply, Matrix.smul_apply]
  push_cast
  simp only [sub_mul]
  rw [Finset.sum_sub_distrib]
  congr 1
  rw [smul_eq_mul]
  calc
    _ = ∑ a, (c : ℂ) *
        (↑((invertPolynomial I q).coeff (pauliExponent J a)) *
          ∏ j : J, pauli (a j) (σ j) (τ j)) := by
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by rw [Finset.mul_sum]

theorem main : AKLT.Blueprint.H1.PairExpansionFromRealizationStatement := by
  intro hNorm π _hπ r I hI hRealize c x hPair
  have hMatrix :
      pauliOperator (reductionVectors π r) (invertPolynomial I (reducedDifference π r c)) =
        rawPauliFunctional (reducedSpinSites π r) (nextStatus π false) (reductionVectors π r) I
            (reducedIntegrand π r false) -
          (c : ℂ) • rawPauliFunctional (reducedSpinSites π r) (nextStatus π true)
            (reductionVectors π r) I (reducedIntegrand π r true) := by
    change pauliOperator _ (invertPolynomial I
      (reducedPolynomial π r false - MvPolynomial.C c * reducedPolynomial π r true)) = _
    rw [pauliOperator_invert_difference, hRealize false, hRealize true]
  rw [hMatrix]
  exact rawDifference_pairExpansion hNorm π r I hI c x hPair

end AKLT.W.H1M052
