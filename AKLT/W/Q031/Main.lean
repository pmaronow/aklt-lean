import AKLT.Blueprint.Q.NodesSplits

noncomputable section

namespace AKLT.W.Q031

private theorem determinant_irreducible :
    Irreducible
      (MvPolynomial.X (0 : Fin 4) * MvPolynomial.X 3 -
        MvPolynomial.X 1 * MvPolynomial.X 2 : MvPolynomial (Fin 4) ℂ) := by
  classical
  have hrel : IsRelPrime
      (MvPolynomial.X (0 : Fin 4) : MvPolynomial (Fin 4) ℂ)
      (-(MvPolynomial.X 1 * MvPolynomial.X 2)) := by
    apply IsRelPrime.neg_right
    apply MvPolynomial.X_prime.irreducible.isRelPrime_iff_not_dvd.mpr
    simp [MvPolynomial.X_dvd_mul_iff, MvPolynomial.X_dvd_X]
  have hvars : (3 : Fin 4) ∉
      (-(MvPolynomial.X 1 * MvPolynomial.X 2) : MvPolynomial (Fin 4) ℂ).vars := by
    rw [MvPolynomial.vars_neg]
    intro h
    have hmul := MvPolynomial.vars_mul
      (MvPolynomial.X (1 : Fin 4) : MvPolynomial (Fin 4) ℂ)
      (MvPolynomial.X (2 : Fin 4)) h
    simp [MvPolynomial.vars_X] at hmul
  simpa only [sub_eq_add_neg] using
    MvPolynomial.irreducible_mul_X_add
      (MvPolynomial.X (0 : Fin 4) : MvPolynomial (Fin 4) ℂ)
      (-(MvPolynomial.X 1 * MvPolynomial.X 2)) (3 : Fin 4)
      (MvPolynomial.X_ne_zero _) (by simp [MvPolynomial.vars_X]) hvars hrel

theorem main : AKLT.Blueprint.Q.FourVariableDeterminantPrimeStatement :=
  determinant_irreducible.prime

#print axioms main

end AKLT.W.Q031
