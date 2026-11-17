STATUS: PROVED

## Delivery

The exact requested closed theorem is proved in `AKLT/W/H1M047/Main.lean`:

```lean
theorem AKLT.W.H1M047.main : AKLT.Blueprint.H1.PauliRotationTransferStatement
```

It has no residual hypotheses. All source edits are confined to `AKLT/W/H1M047/`; the frozen statement is unchanged. No other blueprint leaf is used as a lemma.

## Files

- `AKLT/W/H1M047/Main.lean`: requested theorem, combining coefficient invariance with tensor conjugation and cancelling the unitary tensor power.
- `AKLT/W/H1M047/Basic.lean`: tensor adjoint/unitarity lemmas and explicit rotation coefficients; reuses the useful portion of the earlier attempt.
- `AKLT/W/H1M047/Polynomial.lean`: Pauli-exponent uniqueness and reconstruction, evaluation identities, and rotation coefficient invariance.
- `AKLT/W/H1M047/Tensor.lean`: multiplication of slot-dependent tensors and the complete tensor conjugation expansion.
- `AKLT/W/H1M047/Audit.lean`: exact-type check and axiom checks for every exported theorem.
- `axioms.log`: complete audit output, reproduced below.
- `audit-time.txt`: audit wall time.

## Proof

Every supported vector-affine monomial has a unique Pauli index: at each retained vector slot it is constant or uses exactly one of the three coordinates. This reconstructs the original rational polynomial as a finite sum over Pauli indices.

The rotated coefficient array reconstructs a real polynomial whose evaluation is the original polynomial evaluated at the transpose rotation. The transpose is orthogonal because a one-sided inverse of a finite square matrix is also a right inverse. Orthogonal covariance and multivariate polynomial extensionality over the reals identify the two polynomials; taking coefficients yields `rotation_coefficients_real`, and casting yields `rotation_coefficients`.

The finite tensor expansion is proved independently of covariance. Multiplication of slot tensors is slotwise matrix multiplication, by distributing products over finite sums. Expanding the supplied conjugation coordinates, including the identity Pauli factor, gives `pauli_rotation_expansion`. Coefficient invariance therefore fixes the conjugated Pauli operator. Tensor unitarity cancels its adjoint and gives the requested `Commute` equality. All arguments also cover the empty tensor.

## Exported declarations and statements

All declarations below are in namespace `AKLT.W.H1M047`, with `AKLT.Defs` and `AKLT.Blueprint.H1` open. Proof bodies are omitted here; every theorem body is present in the source.

### Basic.lean

```lean
lemma tensorPower_conjTranspose (J : Finset (Fin 20))
    (g : Matrix (Fin 2) (Fin 2) ℂ) :
    (tensorPowerMatrix J g).conjTranspose = tensorPowerMatrix J g.conjTranspose

lemma tensorPower_left_unitary (J : Finset (Fin 20))
    (g : Matrix (Fin 2) (Fin 2) ℂ)
    (hg : g.conjTranspose * g = 1) :
    (tensorPowerMatrix J g).conjTranspose * tensorPowerMatrix J g = 1

lemma tensorPower_right_unitary (J : Finset (Fin 20))
    (g : Matrix (Fin 2) (Fin 2) ℂ)
    (hg : g.conjTranspose * g = 1) :
    tensorPowerMatrix J g * (tensorPowerMatrix J g).conjTranspose = 1

def pauliRotationCoefficient (R : Matrix (Fin 3) (Fin 3) ℝ)
    (b a : Fin 4) : ℝ

def rotatedPauliCoefficient (J : Finset (Fin 20)) (p : VectorPolynomial)
    (R : Matrix (Fin 3) (Fin 3) ℝ) (b : J → Fin 4) : ℂ

def rotatedPauliOperator (J : Finset (Fin 20)) (p : VectorPolynomial)
    (R : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (J → Fin 2) (J → Fin 2) ℂ
```

### Polynomial.lean

```lean
@[simp] lemma pauliExponent_apply (J : Finset (Fin 20)) (a : J → Fin 4)
    (v : Fin 20 × Fin 3) :
    pauliExponent J a v =
      if h : v.1 ∈ J then if (a ⟨v.1, h⟩).val = v.2.val + 1 then 1 else 0 else 0

lemma pauliExponent_injective (J : Finset (Fin 20)) :
    Function.Injective (pauliExponent J)

lemma affine_exponent_exists (J : Finset (Fin 20))
    (m : (Fin 20 × Fin 3) →₀ ℕ)
    (ha : ∀ j : Fin 20, (∑ k : Fin 3, m (j, k)) ≤ 1)
    (hs : ∀ j : Fin 20, j ∉ J → ∀ k : Fin 3, m (j, k) = 0) :
    ∃ a : J → Fin 4, pauliExponent J a = m

lemma polynomial_pauli_expansion (J : Finset (Fin 20)) (p : VectorPolynomial)
    (ha : VectorAffine p) (hs : SupportedVectors J p) :
    p = ∑ a : J → Fin 4, MvPolynomial.monomial (pauliExponent J a)
      (p.coeff (pauliExponent J a))

lemma eval_pauli_monomial (J : Finset (Fin 20)) (a : J → Fin 4)
    (c : ℝ) (u : Fin 20 → Vec3) :
    MvPolynomial.eval (fun v => u v.1 v.2)
        (MvPolynomial.monomial (pauliExponent J a) c) =
      c * ∏ j : J, pauliCoordinate (u j.val) (a j)

lemma evaluate_pauli_expansion (J : Finset (Fin 20)) (p : VectorPolynomial)
    (ha : VectorAffine p) (hs : SupportedVectors J p) (u : Fin 20 → Vec3) :
    evaluateReduced p u = ∑ a : J → Fin 4,
      (p.coeff (pauliExponent J a) : ℝ) *
        ∏ j : J, pauliCoordinate (u j.val) (a j)

def coefficientPolynomial (J : Finset (Fin 20)) (c : (J → Fin 4) → ℝ) :
    MvPolynomial (Fin 20 × Fin 3) ℝ

lemma coefficientPolynomial_coeff (J : Finset (Fin 20))
    (c : (J → Fin 4) → ℝ) (b : J → Fin 4) :
    (coefficientPolynomial J c).coeff (pauliExponent J b) = c b

lemma coefficientPolynomial_eval (J : Finset (Fin 20))
    (c : (J → Fin 4) → ℝ) (u : Fin 20 → Vec3) :
    MvPolynomial.eval (fun v => u v.1 v.2) (coefficientPolynomial J c) =
      ∑ a : J → Fin 4, c a * ∏ j : J, pauliCoordinate (u j.val) (a j)

lemma pauliCoordinate_rotate (R : Matrix (Fin 3) (Fin 3) ℝ) (u : Vec3) (a : Fin 4) :
    pauliCoordinate (R.transpose.mulVec u) a =
      ∑ b : Fin 4, pauliRotationCoefficient R b a * pauliCoordinate u b

def rotatedCoefficientReal (J : Finset (Fin 20)) (p : VectorPolynomial)
    (R : Matrix (Fin 3) (Fin 3) ℝ) (b : J → Fin 4) : ℝ

lemma rotatedCoefficientReal_eval (J : Finset (Fin 20)) (p : VectorPolynomial)
    (ha : VectorAffine p) (hs : SupportedVectors J p)
    (R : Matrix (Fin 3) (Fin 3) ℝ) (u : Fin 20 → Vec3) :
    MvPolynomial.eval (fun v => u v.1 v.2)
        (coefficientPolynomial J (rotatedCoefficientReal J p R)) =
      evaluateReduced p (fun j => R.transpose.mulVec (u j))

lemma rotation_coefficients_real (J : Finset (Fin 20)) (p : VectorPolynomial)
    (ha : VectorAffine p) (hs : SupportedVectors J p) (hi : OrthogonalInvariant p)
    (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : R.transpose * R = 1) (b : J → Fin 4) :
    rotatedCoefficientReal J p R b = (p.coeff (pauliExponent J b) : ℝ)

lemma rotation_coefficients (J : Finset (Fin 20)) (p : VectorPolynomial)
    (ha : VectorAffine p) (hs : SupportedVectors J p) (hi : OrthogonalInvariant p)
    (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : R.transpose * R = 1) (b : J → Fin 4) :
    rotatedPauliCoefficient J p R b = (p.coeff (pauliExponent J b) : ℂ)
```

### Tensor.lean

```lean
def slotTensor (J : Finset (Fin 20)) (A : J → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (J → Fin 2) (J → Fin 2) ℂ

lemma slotTensor_mul (J : Finset (Fin 20))
    (A B : J → Matrix (Fin 2) (Fin 2) ℂ) :
    slotTensor J A * slotTensor J B = slotTensor J (fun j => A j * B j)

lemma pauliOperator_eq_sum (J : Finset (Fin 20)) (p : VectorPolynomial) :
    pauliOperator J p = ∑ a : J → Fin 4,
      (p.coeff (pauliExponent J a) : ℂ) • slotTensor J (fun j => pauli (a j))

lemma pauli_conjugation_all (g : Matrix (Fin 2) (Fin 2) ℂ)
    (hg : g.conjTranspose * g = 1) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hc : ∀ j : Fin 3, g * pauli ⟨j.val + 1, by omega⟩ * g.conjTranspose =
      ∑ l : Fin 3, (R l j : ℂ) • pauli ⟨l.val + 1, by omega⟩)
    (a : Fin 4) :
    g * pauli a * g.conjTranspose =
      ∑ b : Fin 4, (pauliRotationCoefficient R b a : ℂ) • pauli b

lemma slotTensor_pauli_rotation (J : Finset (Fin 20))
    (R : Matrix (Fin 3) (Fin 3) ℝ) (a : J → Fin 4) :
    slotTensor J (fun j => ∑ b : Fin 4,
        (pauliRotationCoefficient R b (a j) : ℂ) • pauli b) =
      ∑ b : J → Fin 4, (∏ j : J, (pauliRotationCoefficient R (b j) (a j) : ℂ)) •
        slotTensor J (fun j => pauli (b j))

lemma pauli_rotation_expansion (J : Finset (Fin 20)) (p : VectorPolynomial)
    (g : Matrix (Fin 2) (Fin 2) ℂ) (hg : g.conjTranspose * g = 1)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hc : ∀ j : Fin 3, g * pauli ⟨j.val + 1, by omega⟩ * g.conjTranspose =
      ∑ l : Fin 3, (R l j : ℂ) • pauli ⟨l.val + 1, by omega⟩) :
    tensorPowerMatrix J g * pauliOperator J p * (tensorPowerMatrix J g).conjTranspose =
      rotatedPauliOperator J p R
```

### Main.lean

```lean
theorem main : AKLT.Blueprint.H1.PauliRotationTransferStatement
```

## Axioms and exact type

Command: `lake env lean AKLT/W/H1M047/Audit.lean`.

```text
AKLT.W.H1M047.main : AKLT.Blueprint.H1.PauliRotationTransferStatement
'AKLT.W.H1M047.tensorPower_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M047.tensorPower_left_unitary' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M047.tensorPower_right_unitary' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M047.pauliExponent_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M047.pauliExponent_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M047.affine_exponent_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M047.polynomial_pauli_expansion' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M047.eval_pauli_monomial' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M047.evaluate_pauli_expansion' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M047.coefficientPolynomial_coeff' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M047.coefficientPolynomial_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M047.pauliCoordinate_rotate' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M047.rotatedCoefficientReal_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M047.rotation_coefficients_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M047.rotation_coefficients' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M047.slotTensor_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M047.pauliOperator_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M047.pauli_conjugation_all' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M047.slotTensor_pauli_rotation' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M047.pauli_rotation_expansion' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M047.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every exported theorem uses only the permitted axioms `propext`, `Classical.choice`, and `Quot.sound`. The delivered sources contain no proof placeholders, added axioms, forbidden computation shortcuts, or residual statements.

## Builds and timing

- `lake build AKLT.W.H1M047.Basic`: successful; Lean module time 5.5 seconds.
- `/usr/bin/time -f 'ELAPSED=%e' lake build AKLT.W.H1M047.Main`: successful, exit 0; wall time 20.92 seconds. Module times: Tensor 6.6 seconds, Polynomial 7.7 seconds, Main 5.7 seconds.
- `/usr/bin/time -f 'ELAPSED=%e' lake env lean AKLT/W/H1M047/Audit.lean`: successful, exit 0; wall time 7.42 seconds. Exact-type and all axiom checks passed.

## Open issues

None. The two residuals from the earlier attempt are fully discharged by the new polynomial and tensor proofs; the delivered `Main.lean` no longer contains residual declarations or `main_of_residuals`.

## ORCH-SUMMARY

- Delivered `AKLT.W.H1M047.main : AKLT.Blueprint.H1.PauliRotationTransferStatement`.
- Status: PROVED, with no residual premises and no open declarations.
- Completed tensor expansion: `AKLT.W.H1M047.pauli_rotation_expansion`.
- Completed coefficient invariance: `AKLT.W.H1M047.rotation_coefficients`.
- Helpers: Basic.lean, Polynomial.lean, Tensor.lean; verification: Audit.lean.
- Main build passed in 20.92 seconds; exact-type/axiom audit passed in 7.42 seconds.
- All 21 exported theorems use only propext, Classical.choice, Quot.sound.
- No frozen or out-of-scope source files changed; no other blueprint leaf used.
- Earlier partial report remains available as report.luna.md.
- Limitations/deviations: none. Orchestrator may accept the exact requested theorem.
