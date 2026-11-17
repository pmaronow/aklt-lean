module
public import AKLT.Blueprint.H1.NodesV2Structure

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.H1M066

private theorem invert_map (I : Finset (Fin 20))
    (p : MvPolynomial (Fin 20 × Fin 3) ℚ) :
    MvPolynomial.map (Rat.castHom ℝ) (AKLT.Defs.invertPolynomial I p) =
      AKLT.Defs.invertPolynomialReal I (MvPolynomial.map (Rat.castHom ℝ) p) := by
  change MvPolynomial.map (Rat.castHom ℝ)
      (MvPolynomial.bind₁ (fun v => (if v.1 ∈ I then -1 else 1) * MvPolynomial.X v) p) =
    MvPolynomial.bind₁ (fun v => (if v.1 ∈ I then -1 else 1) * MvPolynomial.X v)
      (MvPolynomial.map (Rat.castHom ℝ) p)
  rw [MvPolynomial.map_bind₁]
  have hf : (fun v : Fin 20 × Fin 3 =>
      MvPolynomial.map (Rat.castHom ℝ)
        ((if v.1 ∈ I then -1 else 1) * MvPolynomial.X v)) =
      (fun v => (if v.1 ∈ I then -1 else 1) * MvPolynomial.X v) := by
    funext v
    by_cases hv : v.1 ∈ I
    · simp [hv, MvPolynomial.map_X]
    · simp [hv, MvPolynomial.map_X]
  rw [hf]

private theorem pauli_map (J : Finset (Fin 20))
    (p : MvPolynomial (Fin 20 × Fin 3) ℚ) :
    AKLT.Defs.pauliOperatorReal J (MvPolynomial.map (Rat.castHom ℝ) p) =
      AKLT.Defs.pauliOperator J p := by
  ext σ τ
  simp only [AKLT.Defs.pauliOperatorReal, AKLT.Defs.pauliOperator]
  apply Finset.sum_congr rfl
  intro a ha
  rw [MvPolynomial.coeff_map]
  congr 1

private theorem real_interp (p q : MvPolynomial (Fin 20 × Fin 3) ℝ) (c : ℝ) :
    p - MvPolynomial.C c * q =
      MvPolynomial.C (2 - 3 * c) * (p - MvPolynomial.C (1 / 3 : ℝ) * q) +
        MvPolynomial.C (3 * c - 1) * (p - MvPolynomial.C (2 / 3 : ℝ) * q) := by
  simp only [← MvPolynomial.smul_eq_C_mul]
  module

private theorem pauli_real_linear (J : Finset (Fin 20))
    (p q : MvPolynomial (Fin 20 × Fin 3) ℝ) (a b : ℝ) :
    AKLT.Defs.pauliOperatorReal J (a • p + b • q) =
      (a : ℂ) • AKLT.Defs.pauliOperatorReal J p +
        (b : ℂ) • AKLT.Defs.pauliOperatorReal J q := by
  ext σ τ
  simp only [AKLT.Defs.pauliOperatorReal, Matrix.add_apply, Matrix.smul_apply,
    AddMonoidAlgebra.coeff_add, smul_eq_mul]
  change (∑ i ∈ (Finset.univ : Finset (J → Fin 4)),
      ((a : ℝ) * p.coeff (pauliExponentReal J i) +
        (b : ℝ) * q.coeff (pauliExponentReal J i) : ℝ) *
        (∏ j : J, pauli (i j) (σ j) (τ j))) =
    (a : ℂ) * (∑ i ∈ (Finset.univ : Finset (J → Fin 4)),
      (p.coeff (pauliExponentReal J i) : ℂ) *
        (∏ j : J, pauli (i j) (σ j) (τ j))) +
    (b : ℂ) * (∑ i ∈ (Finset.univ : Finset (J → Fin 4)),
      (q.coeff (pauliExponentReal J i) : ℂ) *
        (∏ j : J, pauli (i j) (σ j) (τ j)))
  calc
    _ = ∑ i ∈ (Finset.univ : Finset (J → Fin 4)),
        ((a : ℂ) * (p.coeff (pauliExponentReal J i) : ℂ) +
          (b : ℂ) * (q.coeff (pauliExponentReal J i) : ℂ)) *
          (∏ j : J, pauli (i j) (σ j) (τ j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      push_cast
      ring
    _ = _ := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring

private theorem invert_real_linear (I : Finset (Fin 20))
    (p q : MvPolynomial (Fin 20 × Fin 3) ℝ) (a b : ℝ) :
    AKLT.Defs.invertPolynomialReal I (a • p + b • q) =
      a • AKLT.Defs.invertPolynomialReal I p + b • AKLT.Defs.invertPolynomialReal I q := by
  simp [AKLT.Defs.invertPolynomialReal, MvPolynomial.smul_eq_C_mul]

private theorem diff_interp (p q : MvPolynomial (Fin 20 × Fin 3) ℚ) (c : ℝ) :
    MvPolynomial.map (Rat.castHom ℝ) p - MvPolynomial.C c * MvPolynomial.map (Rat.castHom ℝ) q =
      MvPolynomial.C (2 - 3 * c) *
          MvPolynomial.map (Rat.castHom ℝ) (p - MvPolynomial.C (1 / 3 : ℚ) * q) +
        MvPolynomial.C (3 * c - 1) *
          MvPolynomial.map (Rat.castHom ℝ) (p - MvPolynomial.C (2 / 3 : ℚ) * q) := by
  simpa [map_sub, map_mul, MvPolynomial.map_C] using
      (real_interp (MvPolynomial.map (Rat.castHom ℝ) p)
        (MvPolynomial.map (Rat.castHom ℝ) q) c)

theorem main : AKLT.Blueprint.H1.RealDifferencePauliInterpolationStatementV2 := by
  intro π r I c
  let p := reducedPolynomial π r false
  let q := reducedPolynomial π r true
  let J := reductionVectors π r
  have hInterp :
      MvPolynomial.map (Rat.castHom ℝ) p - MvPolynomial.C c *
          MvPolynomial.map (Rat.castHom ℝ) q =
        (2 - 3 * c) • MvPolynomial.map (Rat.castHom ℝ)
            (p - MvPolynomial.C (1 / 3 : ℚ) * q) +
          (3 * c - 1) • MvPolynomial.map (Rat.castHom ℝ)
            (p - MvPolynomial.C (2 / 3 : ℚ) * q) := by
    simpa only [MvPolynomial.smul_eq_C_mul] using diff_interp p q c
  have hInv := congrArg (invertPolynomialReal I) hInterp
  rw [invert_real_linear] at hInv
  have hLeft : reducedDifferenceReal π r c =
      MvPolynomial.map (Rat.castHom ℝ) p - MvPolynomial.C c *
        MvPolynomial.map (Rat.castHom ℝ) q := rfl
  have hEndpoints :
      p - MvPolynomial.C (1 / 3 : ℚ) * q = reducedDifference π r (1 / 3) := rfl
  have hEndpoints' :
      p - MvPolynomial.C (2 / 3 : ℚ) * q = reducedDifference π r (2 / 3) := rfl
  change pauliOperatorReal J (invertPolynomialReal I
      (reducedDifferenceReal π r c)) =
    ((2 - 3 * c : ℝ) : ℂ) • pauliOperator J
        (invertPolynomial I (reducedDifference π r (1 / 3))) +
      ((3 * c - 1 : ℝ) : ℂ) • pauliOperator J
        (invertPolynomial I (reducedDifference π r (2 / 3)))
  rw [hLeft, hInv]
  rw [pauli_real_linear]
  rw [hEndpoints, hEndpoints']
  rw [← invert_map I (reducedDifference π r (1 / 3)),
    ← invert_map I (reducedDifference π r (2 / 3))]
  rw [pauli_map, pauli_map]

end AKLT.W.H1M066
