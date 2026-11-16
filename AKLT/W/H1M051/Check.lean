import AKLT.Blueprint.H1.NodesStructure
#check MvPolynomial.C_mul_monomial
#check MvPolynomial.algebraMap_eq
#check MvPolynomial.C_eq_algebraMap
#check MvPolynomial.smul_eq_C_mul
#print MvPolynomial.C_mul_monomial
example (a b : ℚ) (p : MvPolynomial (Fin 20 × Fin 3) ℚ) :
    (a : MvPolynomial (Fin 20 × Fin 3) ℚ) * (b * p) = MvPolynomial.C (a*b) * p := by
  simp [MvPolynomial.algebraMap_eq, ← map_mul, mul_assoc]
example (a b : ℚ) (p : MvPolynomial (Fin 20 × Fin 3) ℚ) :
    MvPolynomial.C a * (b * p) = MvPolynomial.C (a*b) * p := by
  simp [MvPolynomial.algebraMap_eq, ← map_mul, mul_assoc]
