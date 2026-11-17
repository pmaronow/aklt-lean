Exact statement and project-definition excerpts at audited commit

Repository commit: 7a3393531c12080d76aefbdab300ac0c2df834b7

AKLT.Blueprint.H1.PauliHermitianStatement

```lean
def PauliHermitianStatement : Prop :=
  ∀ J : Finset (Fin 20), ∀ p : VectorPolynomial, (pauliOperator J p).IsHermitian
```

AKLT.Blueprint.H1.ReflectionParityStatement

```lean
def ReflectionParityStatement : Prop :=
  ∀ J : Finset (Fin 20), ∀ p : VectorPolynomial, VectorAffine p → SupportedVectors J p →
    OrthogonalInvariant p → ∀ a : J → Fin 4, Odd (pauliYCount J a) → p.coeff (pauliExponent J a) = 0
```

AKLT.Blueprint.H1.PauliRealityStatement

```lean
def PauliRealityStatement : Prop :=
  ∀ J : Finset (Fin 20), ∀ p : VectorPolynomial,
    (∀ a : J → Fin 4, Odd (pauliYCount J a) → p.coeff (pauliExponent J a) = 0) →
    ∀ σ τ, (pauliOperator J p σ τ).im = 0
```

AKLT.Blueprint.H1.InversionCovarianceStatement

```lean
def InversionCovarianceStatement : Prop :=
  ∀ p : VectorPolynomial, OrthogonalInvariant p → ∀ I : Finset (Fin 20),
    OrthogonalInvariant (invertPolynomial I p)
```

AKLT.Blueprint.H1.AdjointPauliCoordinatesStatement

```lean
def AdjointPauliCoordinatesStatement : Prop :=
  ∀ g : Matrix (Fin 2) (Fin 2) ℂ, g.conjTranspose * g = 1 → g.det = 1 →
    ∃ R : Matrix (Fin 3) (Fin 3) ℝ, ∀ j : Fin 3,
      g * pauli ⟨j.val + 1, by omega⟩ * g.conjTranspose =
        ∑ l : Fin 3, (R l j : ℂ) • pauli ⟨l.val + 1, by omega⟩
```

AKLT.Blueprint.H1.AdjointPauliOrthogonalStatement

```lean
def AdjointPauliOrthogonalStatement : Prop :=
  ∀ g : Matrix (Fin 2) (Fin 2) ℂ, g.conjTranspose * g = 1 →
    ∀ R : Matrix (Fin 3) (Fin 3) ℝ,
      (∀ j : Fin 3, g * pauli ⟨j.val + 1, by omega⟩ * g.conjTranspose =
        ∑ l : Fin 3, (R l j : ℂ) • pauli ⟨l.val + 1, by omega⟩) → R.transpose * R = 1
```

AKLT.Blueprint.H1.PauliRotationTransferStatement

```lean
def PauliRotationTransferStatement : Prop :=
  ∀ J : Finset (Fin 20), ∀ p : VectorPolynomial, VectorAffine p → SupportedVectors J p →
    OrthogonalInvariant p → ∀ g : Matrix (Fin 2) (Fin 2) ℂ, g.conjTranspose * g = 1 →
    ∀ R : Matrix (Fin 3) (Fin 3) ℝ, R.transpose * R = 1 →
      (∀ j : Fin 3, g * pauli ⟨j.val + 1, by omega⟩ * g.conjTranspose =
        ∑ l : Fin 3, (R l j : ℂ) • pauli ⟨l.val + 1, by omega⟩) →
      Commute (pauliOperator J p) (tensorPowerMatrix J g)
```

AKLT.Blueprint.H1.CayleyTensorCommutationStatement

```lean
def CayleyTensorCommutationStatement : Prop :=
  ∀ J : Finset (Fin 20), ∀ M : Matrix (J → Fin 2) (J → Fin 2) ℂ,
    (∀ g : Matrix (Fin 2) (Fin 2) ℂ, g.conjTranspose * g = 1 → g.det = 1 →
      Commute M (tensorPowerMatrix J g)) →
    ∀ j : Fin 3, ∀ t : ℝ,
      Commute M (tensorPowerMatrix J (1 + (t : ℂ) • (-Complex.I • pauli ⟨j.val + 1, by omega⟩)))
```

AKLT/Blueprint/H1/Definitions.lean:14 — VectorPolynomial

```lean
abbrev VectorPolynomial := MvPolynomial (Fin 20 × Fin 3) ℚ
abbrev LocalPolynomial := MvPolynomial LocalVariable ℚ
abbrev TensorSpace (J : Finset (Fin 20)) := EuclideanSpace ℂ (J → Fin 2)
```

AKLT/Defs/Moment.lean:9 — Vec3

```lean
abbrev Vec3 := Fin 3 → ℝ
```

AKLT/Defs/Operator.lean:117 — VectorAffine

```lean
def VectorAffine (p : MvPolynomial (Fin 20 × Fin 3) ℚ) : Prop :=
  ∀ m ∈ p.support, ∀ j : Fin 20, (∑ k : Fin 3, m (j, k)) ≤ 1
```

AKLT/Defs/OperatorContracts.lean:36 — SupportedVectors

```lean
def SupportedVectors (J : Finset (Fin 20)) (p : MvPolynomial (Fin 20 × Fin 3) ℚ) : Prop :=
  ∀ m ∈ p.support, ∀ j : Fin 20, j ∉ J → ∀ k : Fin 3, m (j, k) = 0
```

AKLT/Blueprint/H1/Definitions.lean:46 — OrthogonalInvariant

```lean
def OrthogonalInvariant (p : VectorPolynomial) : Prop :=
  ∀ R : Matrix (Fin 3) (Fin 3) ℝ, R.transpose * R = 1 → ∀ u : Fin 20 → Vec3,
    evaluateReduced p (fun j => R.mulVec (u j)) = evaluateReduced p u
```

AKLT/Defs/FiniteNetwork.lean:59 — evaluateReduced

```lean
def evaluateReduced (p : MvPolynomial (Fin 20 × Fin 3) ℚ) (u : Fin 20 → Vec3) : ℝ :=
  MvPolynomial.eval₂ (Rat.castHom ℝ) (fun v => u v.1 v.2) p
```

AKLT/Defs/Operator.lean:121 — invertPolynomial

```lean
def invertPolynomial (I : Finset (Fin 20)) (p : MvPolynomial (Fin 20 × Fin 3) ℚ) :
    MvPolynomial (Fin 20 × Fin 3) ℚ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun v =>
    (if v.1 ∈ I then -1 else 1) * MvPolynomial.X v) p
```

AKLT/Defs/Operator.lean:132 — pauliExponent

```lean
def pauliExponent (J : Finset (Fin 20)) (a : J → Fin 4) : (Fin 20 × Fin 3) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v =>
    if h : v.1 ∈ J then if (a ⟨v.1, h⟩).val = v.2.val + 1 then 1 else 0 else 0
```

AKLT/Defs/Frame.lean:53 — pauli

```lean
def pauli : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => 1
  | 1 => !![0, 1; 1, 0]
  | 2 => !![0, -Complex.I; Complex.I, 0]
  | _ => !![1, 0; 0, -1]
```

AKLT/Defs/Operator.lean:137 — pauliOperator

```lean
def pauliOperator (J : Finset (Fin 20)) (p : MvPolynomial (Fin 20 × Fin 3) ℚ) :
    Matrix (J → Fin 2) (J → Fin 2) ℂ :=
  fun σ τ => ∑ a : J → Fin 4,
    (p.coeff (pauliExponent J a) : ℂ) * ∏ j : J, pauli (a j) (σ j) (τ j)
```

AKLT/Blueprint/H1/Definitions.lean:158 — pauliYCount

```lean
def pauliYCount (J : Finset (Fin 20)) (a : J → Fin 4) : ℕ :=
  (Finset.univ.filter fun j => a j = 2).card
```

AKLT/Defs/OperatorContracts.lean:79 — tensorPowerMatrix

```lean
def tensorPowerMatrix (J : Finset (Fin 20)) (g : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (J → Fin 2) (J → Fin 2) ℂ := fun σ τ => ∏ j : J, g (σ j) (τ j)
```
