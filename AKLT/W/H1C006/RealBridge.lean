module
public import AKLT.W.H1C006.Dependencies

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs AKLT.Blueprint.H1

namespace AKLT.W.H1C006

theorem invert_map_real (I : Finset (Fin 20)) (p : VectorPolynomial) :
    invertPolynomialReal I (MvPolynomial.map (Rat.castHom ℝ) p) =
      MvPolynomial.map (Rat.castHom ℝ) (invertPolynomial I p) := by
  change MvPolynomial.bind₁
      (fun v => (if v.1 ∈ I then -1 else 1) * MvPolynomial.X v)
      (MvPolynomial.map (Rat.castHom ℝ) p) =
    MvPolynomial.map (Rat.castHom ℝ)
      (MvPolynomial.bind₁ (fun v => (if v.1 ∈ I then -1 else 1) * MvPolynomial.X v) p)
  rw [MvPolynomial.map_bind₁]
  have hf : (fun v : Fin 20 × Fin 3 => MvPolynomial.map (Rat.castHom ℝ)
      ((if v.1 ∈ I then -1 else 1) * MvPolynomial.X v)) =
      (fun v => (if v.1 ∈ I then -1 else 1) * MvPolynomial.X v) := by
    funext v
    by_cases hv : v.1 ∈ I <;> simp [hv, MvPolynomial.map_X]
  rw [hf]

theorem pauli_map_real (J : Finset (Fin 20)) (p : VectorPolynomial) :
    pauliOperatorReal J (MvPolynomial.map (Rat.castHom ℝ) p) = pauliOperator J p := by
  ext σ τ
  simp only [pauliOperatorReal, pauliOperator]
  apply Finset.sum_congr rfl
  intro a _
  rw [MvPolynomial.coeff_map]
  congr 1

theorem rational_ball_nonnegative (J : Finset (Fin 20)) (p : VectorPolynomial)
    (ha : VectorAffine p) (hs : SupportedVectors J p)
    (I : Finset (Fin 20)) (hI : I ⊆ J)
    (hM : (pauliOperator J (invertPolynomial I p)).PosSemidef)
    (u : Fin 20 → Vec3) (hu : ∀ j ∈ J, normSq (u j) ≤ 1) :
    0 ≤ evaluateReduced p u := by
  obtain ⟨haR, hsR⟩ := H1M061.main p J ha hs
  have hMR : (pauliOperatorReal J
      (invertPolynomialReal I (MvPolynomial.map (Rat.castHom ℝ) p))).PosSemidef := by
    rw [invert_map_real, pauli_map_real]
    exact hM
  have hb := (inversionReal.2 20 J _ haR hsR I hI).2 hMR u hu
  rwa [H1M062.main] at hb

end AKLT.W.H1C006
