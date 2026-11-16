import AKLT.Cert.H1.Production.Leaves

namespace AKLT.W.H1C022

open AKLT.Defs
open scoped BigOperators

private lemma rationalOperatorEntry_C_mul (J : Finset (Fin 20))
    (p : MvPolynomial (Fin 20 × Fin 3) ℚ) (k : ℚ) (σ τ : J → Fin 2) :
    rationalOperatorEntry J (MvPolynomial.C k * p) σ τ =
      k * rationalOperatorEntry J p σ τ := by
  simp only [rationalOperatorEntry, MvPolynomial.coeff_C_mul,
    Finset.mul_sum, mul_assoc]

theorem main : AKLT.Cert.H1.Production.Leaves.sectorLinearity := by
  classical
  intro π r ε a b k p
  unfold rationalSectorEntry
  calc
    (∑ σ, ∑ τ,
        (exchangeBasisVector π r ε a.val σ : ℚ) *
          rationalOperatorEntry (reductionVectors π r) (MvPolynomial.C k * p) σ τ *
            (exchangeBasisVector π r ε b.val τ : ℚ)) =
      ∑ σ, ∑ τ, k *
        ((exchangeBasisVector π r ε a.val σ : ℚ) *
          rationalOperatorEntry (reductionVectors π r) p σ τ *
            (exchangeBasisVector π r ε b.val τ : ℚ)) := by
      apply Finset.sum_congr rfl
      intro σ hσ
      apply Finset.sum_congr rfl
      intro τ hτ
      rw [rationalOperatorEntry_C_mul]
      ring
    _ = k * ∑ σ, ∑ τ,
        (exchangeBasisVector π r ε a.val σ : ℚ) *
          rationalOperatorEntry (reductionVectors π r) p σ τ *
            (exchangeBasisVector π r ε b.val τ : ℚ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [Finset.mul_sum]

end AKLT.W.H1C022
