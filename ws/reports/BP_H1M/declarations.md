# H1 declaration catalog

Namespace: `AKLT.Blueprint.H1`. Imports and open scopes are in the source files.

```lean
def H1FiniteDataStatementV2 : Prop :=
  ∀ π : PatternData, π.Covered → ∃ r : Representation, ∃ I : Finset (Fin 20),
    GroupInversion π r I ∧ ∃ D₀ : ℕ, ClearsDenominator π r D₀ ∧
      SectorWitnesses π r I D₀ (h1Numerator π) (h1Denominator π)
```

```lean
def CertificateStatementV2 : Prop := AKLT.Blueprint.Top.CertificateStatement ∧ H1FiniteDataStatementV2
```

```lean
def ThresholdSymmetryStatement : Prop :=
  ∀ π : PatternData, π.Covered → ∀ r : Representation,
    ∀ I : Finset (Fin 20), GroupInversion π r I → ∀ D₀ : ℕ, ClearsDenominator π r D₀ →
    ∀ p q : ℕ, 0 < p → 0 < q → (p : ℚ) / q < 1 → ∀ ε : ExchangeSigns π,
      (thresholdSectorMatrix π r ε I D₀ p q).IsSymm
```

```lean
def CoveredSlotEnumerationStatement : Prop :=
  ∀ π : PatternData, π.Covered → ∀ m : Fin 20 → UnitVector,
    ∀ x ∈ templateCorners ∪ templateTips, π.statusAt x ≠ .X →
    (∃ a : Fin 3 → UnitVector, π.statusAt x = .U ∧ replacementRadius π x = 3 / 5 ∧
      coveredSiteField m x = localProduct (fun j => (a j).val)) ∨
    (∃ a : Fin 2 → UnitVector, (π.statusAt x = .U ∨ π.statusAt x = .D) ∧
      replacementRadius π x = (if π.statusAt x = .U then 1 / 2 else 1 / 3) ∧
      coveredSiteField m x = localProduct (fun j => (a j).val))
```

```lean
def CornerMeanBoundsStatement : Prop :=
  MonomialMoments → ∀ a : Fin 2 → UnitVector, ∀ s : Status, s = .U ∨ s = .D →
    0 < siteFunctional s (localProduct (fun j => (a j).val)) ∧
    normSq (localMean s (fun j => (a j).val)) ≤
      (if s = .U then (1 / 2 : ℝ) else 1 / 3) ^ 2
```

```lean
def NormalizedMeanFactorStatement : Prop :=
  ∀ k : ℕ, ∀ a : Fin k → Vec3, ∀ s : Status, ∀ ρ : ℝ, 0 < ρ →
    0 < siteFunctional s (localProduct a) → normSq (localMean s a) ≤ ρ ^ 2 →
    ∃ A : ℝ, 0 < A ∧ ∃ u : Vec3, normSq u ≤ 1 ∧
      ∀ v : Vec3, normSq v ≤ 1 →
        siteFunctional s (fun n => localProduct a n * (1 + dot n v)) = A * (1 + ρ * dot u v)
```

```lean
def PassageSiteMomentsStatement : Prop :=
  MonomialMoments → ∀ a b o : Vec3,
    siteFunctional .U (fun n => (1 + dot n a) * (1 + dot n b) * (1 + dot n o)) =
      1 + (dot a b + dot a o + dot b o) / 3 ∧
    siteFunctional .D (fun n => (1 + dot n a) * (1 + dot n b)) = 1 + dot a b / 5
```

```lean
def PassageFubiniStatement : Prop :=
  (∀ a b o : Vec3,
    siteFunctional .U (fun n => (1 + dot n a) * (1 + dot n b) * (1 + dot n o)) =
      1 + (dot a b + dot a o + dot b o) / 3 ∧
    siteFunctional .D (fun n => (1 + dot n a) * (1 + dot n b)) = 1 + dot a b / 5) →
  ∀ π : PatternData, π.Covered → ∀ m : Fin 20 → UnitVector, ∀ f g : Plane,
    PassageNeighbours π f g →
    patternCurrent π m = withoutPassageFunctional π m (passageI π.outgoing.step f g) ∧
    patternNext π m = withoutPassageFunctional π m (passageJ f g)
```

```lean
def PassageNetworkPositiveStatement : Prop :=
  (∀ n : ℕ, ∀ D : FiniteSpinNetwork n, D.Valid → 0 < D.partition true (fun _ => 1)) →
  ∀ π : PatternData, π.Covered → ∀ m : Fin 20 → UnitVector,
    0 < withoutPassageFunctional π m (fun _ => 1)
```

```lean
def PassageNextLowerBoundStatement : Prop :=
  (∀ j : IcoLetter, normSq (icoVector j) = 1) →
  ∀ π : PatternData, π.Covered → ∀ m : Fin 20 → UnitVector, ∀ f g : Plane,
    (4 / 5 : ℝ) * withoutPassageFunctional π m (fun _ => 1) ≤
      withoutPassageFunctional π m (passageJ f g)
```

```lean
def PassageSubtractionStatement : Prop :=
  ∀ π : PatternData, ∀ m : Fin 20 → UnitVector, ∀ F G : (Plane → Vec3) → ℝ, ∀ c : ℝ,
    withoutPassageFunctional π m F - c * withoutPassageFunctional π m G =
      withoutPassageFunctional π m (fun n => F n - c * G n)
```

```lean
def OriginalDegreeStatement : Prop :=
  ∀ π : PatternData, π.Covered → ∀ next : Bool,
    InternalAdmissible π.active (originalIntegrand π next)
```

```lean
def OriginalFactorStructureStatement : Prop :=
  ∀ π : PatternData, ∀ next : Bool,
    LocalVectorAffine (originalIntegrand π next) ∧ IntegrandInvariant (originalIntegrand π next)
```

```lean
def OriginalRawEvaluationStatement : Prop :=
  ∀ π : PatternData, ∀ next : Bool, ∀ m : Fin 20 → UnitVector,
    rawFunctional π.active (nextStatus π next) (originalIntegrand π next) (fun j => (m j).val) =
      if next then patternNext π m else patternCurrent π m
```

```lean
def MomentContractionStatement : Prop :=
  MonomialMoments → ∀ V : Finset Plane, ∀ s : Plane → Status,
    (∀ x ∈ V, s x = .U ∨ s x = .D) → ∀ p : LocalPolynomial,
    InternalAdmissible V p → ∀ u : Fin 20 → Vec3,
      evaluateReduced (contractSpins V s p) u = rawFunctional V s p u
```

```lean
def MomentCovarianceTransferStatement : Prop :=
  MonomialMoments → ProductMomentCovariance → ∀ V : Finset Plane, ∀ s : Plane → Status,
    (∀ x ∈ V, s x = .U ∨ s x = .D) → ∀ p : LocalPolynomial,
    InternalAdmissible V p → IntegrandInvariant p → OrthogonalInvariant (contractSpins V s p)
```

```lean
def ContractionAffineStatement : Prop :=
  ∀ V : Finset Plane, ∀ s : Plane → Status, ∀ p : LocalPolynomial,
    LocalVectorAffine p → VectorAffine (contractSpins V s p)
```

```lean
def ContractionSupportStatement : Prop :=
  ∀ V : Finset Plane, ∀ s : Plane → Status, ∀ p : LocalPolynomial,
    ∀ J : Finset (Fin 20), LocalSupportedVectors J p → SupportedVectors J (contractSpins V s p)
```

```lean
def ActiveStatusesStatement : Prop :=
  ∀ π : PatternData, ∀ next : Bool, ∀ x ∈ π.active, nextStatus π next x = .U ∨ nextStatus π next x = .D
```

```lean
def BlochAlgebraStatement : Prop :=
  ∀ u : Vec3, (blochMatrix u).IsHermitian ∧
    blochMatrix u * blochMatrix u = (normSq u : ℂ) • 1 ∧ (blochMatrix u).trace = 0
```

```lean
def BlochPositivityStatement : Prop :=
  ∀ A : Matrix (Fin 2) (Fin 2) ℂ, A.IsHermitian → ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
    A * A = (r : ℂ) • 1 → ((1 / 2 : ℂ) • (1 + A)).PosSemidef
```

```lean
def SinglePauliTraceStatement : Prop :=
  ∀ a : Fin 4, ∀ u : Vec3, (pauli a * spinDensity u).trace = (pauliCoordinate u a : ℂ)
```

```lean
def PauliExpansionStatement : Prop :=
  ∀ J : Finset (Fin 20), ∀ p : VectorPolynomial, VectorAffine p → SupportedVectors J p →
    ∀ u : Fin 20 → Vec3, evaluateReduced p u =
      ∑ a : J → Fin 4, (p.coeff (pauliExponent J a) : ℝ) * ∏ j : J, pauliCoordinate (u j.val) (a j)
```

```lean
def PauliProductTraceStatement : Prop :=
  (∀ a : Fin 4, ∀ u : Vec3, (pauli a * spinDensity u).trace = (pauliCoordinate u a : ℂ)) →
  ∀ J : Finset (Fin 20), ∀ p : VectorPolynomial, ∀ u : Fin 20 → Vec3,
    (pauliOperator J p * productDensity J u).trace =
      ((∑ a : J → Fin 4, (p.coeff (pauliExponent J a) : ℝ) *
        ∏ j : J, pauliCoordinate (u j.val) (a j) : ℝ) : ℂ)
```

```lean
def InversionPolynomialStatement : Prop :=
  ∀ J I : Finset (Fin 20), ∀ p : VectorPolynomial, VectorAffine p → SupportedVectors J p →
    VectorAffine (invertPolynomial I p) ∧ SupportedVectors J (invertPolynomial I p) ∧
      ∀ u : Fin 20 → Vec3, evaluateReduced (invertPolynomial I p) (invertVectors I u) = evaluateReduced p u
```

```lean
def ProductDensityPositiveStatement : Prop :=
  ∀ J : Finset (Fin 20), ∀ u : Fin 20 → Vec3,
    (∀ j ∈ J, (spinDensity (u j)).PosSemidef) → (productDensity J u).PosSemidef
```

```lean
def TraceProductPositiveStatement : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n],
    ∀ A B : Matrix n n ℂ, A.PosSemidef → B.PosSemidef → 0 ≤ (A * B).trace.re
```

```lean
def InversionBallStatement : Prop :=
  ∀ I : Finset (Fin 20), ∀ u : Fin 20 → Vec3, ∀ j : Fin 20,
    normSq (invertVectors I u j) = normSq (u j)
```

```lean
def ReducedDegreeStatement : Prop :=
  ∀ π : PatternData, π.Covered → ∀ r : Representation, ∀ next : Bool,
    InternalAdmissible (reducedSpinSites π r) (reducedIntegrand π r next)
```

```lean
def ReducedFactorStructureStatement : Prop :=
  ∀ π : PatternData, π.Covered → ∀ r : Representation, ∀ next : Bool,
    LocalVectorAffine (reducedIntegrand π r next) ∧
    IntegrandInvariant (reducedIntegrand π r next) ∧
    LocalSupportedVectors (reductionVectors π r) (reducedIntegrand π r next)
```

```lean
def PeripheralGeometryStatement : Prop :=
  ∀ π : PatternData, π.Covered → ∀ r : Representation, PeripheralGeometry π r
```

```lean
def PeripheralFubiniStatement : Prop :=
  ∀ π : PatternData, π.Covered → ∀ r : Representation, PeripheralGeometry π r →
    ∀ next : Bool, ∀ m : Fin 20 → UnitVector,
      (if next then patternNext π m else patternCurrent π m) = separatedLeafFunctional π r next m
```

```lean
def PeripheralAssignmentStatement : Prop :=
  (∀ j : IcoLetter, normSq (icoVector j) = 1) →
  ∀ π : PatternData, π.Covered → ∀ r : Representation, PeripheralGeometry π r →
    ∀ m : Fin 20 → UnitVector, LeafRule π m →
      ∃ K : ℝ, 0 < K ∧ ∃ u : Fin 20 → Vec3, (∀ j, normSq (u j) ≤ 1) ∧
        ∀ next : Bool, separatedLeafFunctional π r next m = K *
          rawFunctional (reducedSpinSites π r) (nextStatus π next) (reducedIntegrand π r next) u
```

```lean
def SimultaneousLeafReconstructionStatement : Prop :=
  (∀ j : IcoLetter, normSq (icoVector j) = 1) →
  ∀ π : PatternData, π.Covered → ∀ r : Representation,
    (∀ next : Bool, ∀ u : Fin 20 → Vec3,
      evaluateReduced (reducedPolynomial π r next) u =
        rawFunctional (reducedSpinSites π r) (nextStatus π next) (reducedIntegrand π r next) u) →
    ∀ m : Fin 20 → UnitVector, LeafRule π m →
      ∃ K : ℝ, 0 < K ∧ ∃ u : Fin 20 → Vec3,
        (∀ j, normSq (u j) ≤ 1) ∧
        patternCurrent π m = K * evaluateReduced (reducedPolynomial π r false) u ∧
        patternNext π m = K * evaluateReduced (reducedPolynomial π r true) u
```

```lean
def BallChordStatement : Prop := ∀ v : Vec3, normSq v ≤ 1 → UnitChord v
```

```lean
def AffineEvaluationStatement : Prop :=
  ∀ p : VectorPolynomial, VectorAffine p → SeparatelyAffine (evaluateReduced p)
```

```lean
def ProductBallNonnegativeStatement : Prop :=
  (∀ v : Vec3, normSq v ≤ 1 → UnitChord v) →
  ∀ F : (Fin 20 → Vec3) → ℝ, SeparatelyAffine F →
    (∀ u : Fin 20 → UnitVector, 0 ≤ F (fun j => (u j).val)) →
    ∀ u : Fin 20 → Vec3, (∀ j, normSq (u j) ≤ 1) → 0 ≤ F u
```

```lean
def DifferenceStructureStatement : Prop :=
  ∀ J : Finset (Fin 20), ∀ p q : VectorPolynomial, ∀ c : ℚ,
    VectorAffine p → VectorAffine q → OrthogonalInvariant p → OrthogonalInvariant q →
    SupportedVectors J p → SupportedVectors J q →
      VectorAffine (p - MvPolynomial.C c * q) ∧
      OrthogonalInvariant (p - MvPolynomial.C c * q) ∧
      SupportedVectors J (p - MvPolynomial.C c * q)
```

```lean
def ReducedStructureStatement : Prop :=
  ∀ π : PatternData, π.Covered → ∀ r : Representation, ∀ c : ℚ,
    VectorAffine (reducedDifference π r c) ∧ OrthogonalInvariant (reducedDifference π r c) ∧
      SupportedVectors (reductionVectors π r) (reducedDifference π r c)
```

```lean
def DifferenceEvaluationStatement : Prop :=
  ∀ π : PatternData, ∀ r : Representation, ∀ c : ℚ, ∀ u : Fin 20 → Vec3,
    evaluateReduced (reducedDifference π r c) u =
      evaluateReduced (reducedPolynomial π r false) u -
        (c : ℝ) * evaluateReduced (reducedPolynomial π r true) u
```

```lean
def SectorSpinStableStatement : Prop :=
  ∀ π : PatternData, ∀ r : Representation, ∀ ε : ExchangeSigns π,
    SpinStable (reductionVectors π r) (exchangeSpace π r ε)
```

```lean
def SectorWeightBasisStatement : Prop :=
  ∀ π : PatternData, ∀ r : Representation, ∀ ε : ExchangeSigns π,
    ∀ b : ExchangeBasis π r ε,
      totalSpinZ (reductionVectors π r) (sectorVector π r ε b) =
        (exchangeWeight π r ε b : ℂ) • sectorVector π r ε b ∧
      ∃ z : ℤ, (exchangeWeight π r ε b : ℝ) = (centralWeight π r : ℝ) + z
```

```lean
def SpanWeightLatticeStatement : Prop :=
  ∀ J : Finset (Fin 20), ∀ (β : Type) [Fintype β],
    ∀ v : β → TensorSpace J, ∀ w : β → ℝ, ∀ κ : ℝ,
      (∀ b, totalSpinZ J (v b) = (w b : ℂ) • v b) →
      (∀ b, ∃ z : ℤ, w b = κ + z) →
      ∀ ψ ∈ Submodule.span ℂ (Set.range v), ψ ≠ 0 → ∀ m : ℝ,
        totalSpinZ J ψ = (m : ℂ) • ψ → ∃ z : ℤ, m = κ + z
```

```lean
def SpinAdjointStatement : Prop :=
  ∀ J : Finset (Fin 20), ∀ ψ χ : TensorSpace J,
    inner ℂ (totalSpinZ J ψ) χ = inner ℂ ψ (totalSpinZ J χ) ∧
    inner ℂ (totalSpinPlus J ψ) χ = inner ℂ ψ (totalSpinMinus J χ)
```

```lean
def SpinCommutatorStatement : Prop :=
  ∀ J : Finset (Fin 20), ∀ ψ : TensorSpace J,
    totalSpinZ J (totalSpinPlus J ψ) - totalSpinPlus J (totalSpinZ J ψ) = totalSpinPlus J ψ ∧
    totalSpinZ J (totalSpinMinus J ψ) - totalSpinMinus J (totalSpinZ J ψ) = -totalSpinMinus J ψ ∧
    totalSpinPlus J (totalSpinMinus J ψ) - totalSpinMinus J (totalSpinPlus J ψ) =
      (2 : ℂ) • totalSpinZ J ψ
```

```lean
def WeightLadderTransferStatement : Prop :=
  ∀ J : Finset (Fin 20),
    (∀ ψ χ : TensorSpace J,
      inner ℂ (totalSpinZ J ψ) χ = inner ℂ ψ (totalSpinZ J χ) ∧
      inner ℂ (totalSpinPlus J ψ) χ = inner ℂ ψ (totalSpinMinus J χ)) →
    (∀ ψ : TensorSpace J,
      totalSpinZ J (totalSpinPlus J ψ) - totalSpinPlus J (totalSpinZ J ψ) = totalSpinPlus J ψ ∧
      totalSpinZ J (totalSpinMinus J ψ) - totalSpinMinus J (totalSpinZ J ψ) = -totalSpinMinus J ψ ∧
      totalSpinPlus J (totalSpinMinus J ψ) - totalSpinMinus J (totalSpinPlus J ψ) =
        (2 : ℂ) • totalSpinZ J ψ) → WeightLadder J
```

```lean
def CommonWeightEigenvectorStatement : Prop :=
  ∀ J : Finset (Fin 20), ∀ S : Submodule ℂ (TensorSpace J),
    ∀ O : Module.End ℂ (TensorSpace J), (∀ ψ ∈ S, O ψ ∈ S) →
      (∀ ψ ∈ S, ∀ χ ∈ S, inner ℂ (O ψ) χ = inner ℂ ψ (O χ)) →
      (∀ ψ ∈ S, totalSpinZ J ψ ∈ S) →
      (∀ ψ ∈ S, ∀ χ ∈ S, inner ℂ (totalSpinZ J ψ) χ = inner ℂ ψ (totalSpinZ J χ)) →
      (∀ ψ ∈ S, O (totalSpinZ J ψ) = totalSpinZ J (O ψ)) →
      ∀ μ ∈ eigenvaluesOn S O, ∃ v ∈ S, v ≠ 0 ∧ O v = μ • v ∧
        ∃ m : ℝ, totalSpinZ J v = (m : ℂ) • v
```

```lean
def LadderWalkStatement : Prop :=
  ∀ J : Finset (Fin 20), ∀ S : Submodule ℂ (TensorSpace J), ∀ κ : ℝ,
    (κ = 0 ∨ κ = 1 / 2) → SpinStable J S → WeightLadder J →
    ∀ O : Module.End ℂ (TensorSpace J),
      (∀ ψ ∈ S, O (totalSpinPlus J ψ) = totalSpinPlus J (O ψ)) →
      (∀ ψ ∈ S, O (totalSpinMinus J ψ) = totalSpinMinus J (O ψ)) →
      ∀ μ : ℂ, ∀ v ∈ S, v ≠ 0 → O v = μ • v → ∀ m : ℝ,
      totalSpinZ J v = (m : ℂ) • v → (∃ z : ℤ, m = κ + z) →
      ∃ w ∈ S, w ≠ 0 ∧ O w = μ • w ∧ totalSpinZ J w = (κ : ℂ) • w
```

```lean
def PositiveSpectrumStatement : Prop :=
  ∀ J : Finset (Fin 20), ∀ S : Submodule ℂ (TensorSpace J),
    ∀ O : Module.End ℂ (TensorSpace J), (∀ ψ ∈ S, O ψ ∈ S) →
      (∀ ψ ∈ S, ∀ χ ∈ S, inner ℂ (O ψ) χ = inner ℂ ψ (O χ)) →
      (PositiveOn S O ↔ ∀ μ ∈ eigenvaluesOn S O, 0 < μ.re)
```

```lean
def CentralWeightHalfStatement : Prop :=
  ∀ π : PatternData, ∀ r : Representation,
    (centralWeight π r : ℝ) = 0 ∨ (centralWeight π r : ℝ) = 1 / 2
```

```lean
def PauliHermitianStatement : Prop :=
  ∀ J : Finset (Fin 20), ∀ p : VectorPolynomial, (pauliOperator J p).IsHermitian
```

```lean
def ReflectionParityStatement : Prop :=
  ∀ J : Finset (Fin 20), ∀ p : VectorPolynomial, VectorAffine p → SupportedVectors J p →
    OrthogonalInvariant p → ∀ a : J → Fin 4, Odd (pauliYCount J a) → p.coeff (pauliExponent J a) = 0
```

```lean
def PauliRealityStatement : Prop :=
  ∀ J : Finset (Fin 20), ∀ p : VectorPolynomial,
    (∀ a : J → Fin 4, Odd (pauliYCount J a) → p.coeff (pauliExponent J a) = 0) →
    ∀ σ τ, (pauliOperator J p σ τ).im = 0
```

```lean
def InversionCovarianceStatement : Prop :=
  ∀ p : VectorPolynomial, OrthogonalInvariant p → ∀ I : Finset (Fin 20),
    OrthogonalInvariant (invertPolynomial I p)
```

```lean
def AdjointPauliCoordinatesStatement : Prop :=
  ∀ g : Matrix (Fin 2) (Fin 2) ℂ, g.conjTranspose * g = 1 → g.det = 1 →
    ∃ R : Matrix (Fin 3) (Fin 3) ℝ, ∀ j : Fin 3,
      g * pauli ⟨j.val + 1, by omega⟩ * g.conjTranspose =
        ∑ l : Fin 3, (R l j : ℂ) • pauli ⟨l.val + 1, by omega⟩
```

```lean
def AdjointPauliOrthogonalStatement : Prop :=
  ∀ g : Matrix (Fin 2) (Fin 2) ℂ, g.conjTranspose * g = 1 →
    ∀ R : Matrix (Fin 3) (Fin 3) ℝ,
      (∀ j : Fin 3, g * pauli ⟨j.val + 1, by omega⟩ * g.conjTranspose =
        ∑ l : Fin 3, (R l j : ℂ) • pauli ⟨l.val + 1, by omega⟩) → R.transpose * R = 1
```

```lean
def PauliRotationTransferStatement : Prop :=
  ∀ J : Finset (Fin 20), ∀ p : VectorPolynomial, VectorAffine p → SupportedVectors J p →
    OrthogonalInvariant p → ∀ g : Matrix (Fin 2) (Fin 2) ℂ, g.conjTranspose * g = 1 →
    ∀ R : Matrix (Fin 3) (Fin 3) ℝ, R.transpose * R = 1 →
      (∀ j : Fin 3, g * pauli ⟨j.val + 1, by omega⟩ * g.conjTranspose =
        ∑ l : Fin 3, (R l j : ℂ) • pauli ⟨l.val + 1, by omega⟩) →
      Commute (pauliOperator J p) (tensorPowerMatrix J g)
```

```lean
def CayleyTensorCommutationStatement : Prop :=
  ∀ J : Finset (Fin 20), ∀ M : Matrix (J → Fin 2) (J → Fin 2) ℂ,
    (∀ g : Matrix (Fin 2) (Fin 2) ℂ, g.conjTranspose * g = 1 → g.det = 1 →
      Commute M (tensorPowerMatrix J g)) →
    ∀ j : Fin 3, ∀ t : ℝ,
      Commute M (tensorPowerMatrix J (1 + (t : ℂ) • (-Complex.I • pauli ⟨j.val + 1, by omega⟩)))
```

```lean
def TensorLinearCoefficientStatement : Prop :=
  ∀ J : Finset (Fin 20), ∀ M : Matrix (J → Fin 2) (J → Fin 2) ℂ,
    ∀ A : Matrix (Fin 2) (Fin 2) ℂ,
      (∀ t : ℝ, Commute M (tensorPowerMatrix J (1 + (t : ℂ) • A))) →
      Commute M (∑ j : J, tokenMatrix J j A)
```

```lean
def SpinGeneratorTransferStatement : Prop :=
  ∀ J : Finset (Fin 20), ∀ M : Matrix (J → Fin 2) (J → Fin 2) ℂ,
    (∀ k : Fin 3, Commute M (∑ j : J, tokenMatrix J j (-Complex.I • pauli ⟨k.val + 1, by omega⟩))) →
    Commute (Matrix.toEuclideanLin M) (totalSpinZ J) ∧
    Commute (Matrix.toEuclideanLin M) (totalSpinPlus J) ∧
    Commute (Matrix.toEuclideanLin M) (totalSpinMinus J)
```

```lean
def MomentPauliInterchangeStatement : Prop :=
  MonomialMoments → ∀ V : Finset Plane, ∀ s : Plane → Status,
    (∀ x ∈ V, s x = .U ∨ s x = .D) → ∀ p : LocalPolynomial,
    InternalAdmissible V p → ∀ J I : Finset (Fin 20),
      pauliOperator J (invertPolynomial I (contractSpins V s p)) = rawPauliFunctional V s J I p
```

```lean
def PairExpansionFromRealizationStatement : Prop :=
  (∀ j : IcoLetter, normSq (icoVector j) = 1) →
  ∀ π : PatternData, π.Covered → ∀ r : Representation,
    ∀ I : Finset (Fin 20), GroupInversion π r I →
    (∀ next : Bool, pauliOperator (reductionVectors π r) (invertPolynomial I (reducedPolynomial π r next)) =
      rawPauliFunctional (reducedSpinSites π r) (nextStatus π next) (reductionVectors π r) I
        (reducedIntegrand π r next)) →
    ∀ c : ℚ, ∀ x : reductionGroups π, ∀ h : groupIsPair π r x.val = true,
      PairExpansion (reductionVectors π r) (leaderToken π r x) (secondToken π r x h)
        (Matrix.toEuclideanLin (pauliOperator (reductionVectors π r)
          (invertPolynomial I (reducedDifference π r c)))) (π.statusAt x.val = .U)
```

```lean
def RetainedPairExpansionStatement : Prop :=
  MonomialMoments → (∀ j : IcoLetter, normSq (icoVector j) = 1) →
  ∀ π : PatternData, π.Covered → ∀ r : Representation,
    (∀ next : Bool, InternalAdmissible (reducedSpinSites π r) (reducedIntegrand π r next)) →
    ∀ I : Finset (Fin 20), GroupInversion π r I → ∀ c : ℚ,
    ∀ x : reductionGroups π, ∀ h : groupIsPair π r x.val = true,
      PairExpansion (reductionVectors π r) (leaderToken π r x) (secondToken π r x h)
        (Matrix.toEuclideanLin (pauliOperator (reductionVectors π r)
          (invertPolynomial I (reducedDifference π r c)))) (π.statusAt x.val = .U)
```

```lean
def UnitPairSupportStatement : Prop :=
  ∀ J : Finset (Fin 20), ∀ j k : J, j ≠ k → ∀ η : ℝ, η ^ 2 = 1 →
    ∀ n : Vec3, normSq n = 1 →
      symmetricPairProjection J j k * pairTerm J j k η n = pairTerm J j k η n ∧
      pairTerm J j k η n * symmetricPairProjection J j k = pairTerm J j k η n
```

```lean
def EqualPairExchangeStatement : Prop :=
  ∀ J : Finset (Fin 20), ∀ j k : J, ∀ η : ℝ, ∀ n : Vec3,
    Commute (pairTerm J j k η n) (exchangeOperator J j k)
```

```lean
def PairExpansionTransferStatement : Prop :=
  ∀ J : Finset (Fin 20), ∀ j k : J, ∀ O : Module.End ℂ (TensorSpace J), ∀ unitOnly : Prop,
    PairExpansion J j k O unitOnly →
    (∀ η : ℝ, η ^ 2 = 1 → ∀ n : Vec3, normSq n = 1 →
      symmetricPairProjection J j k * pairTerm J j k η n = pairTerm J j k η n ∧
      pairTerm J j k η n * symmetricPairProjection J j k = pairTerm J j k η n) →
    (∀ η : ℝ, ∀ n : Vec3, Commute (pairTerm J j k η n) (exchangeOperator J j k)) →
    (unitOnly → O = symmetricPairProjection J j k * O * symmetricPairProjection J j k) ∧
    Commute O (exchangeOperator J j k)
```

```lean
def PairTokensDistinctStatement : Prop :=
  ∀ π : PatternData, ∀ r : Representation, ∀ x : reductionGroups π,
    ∀ h : groupIsPair π r x.val = true, leaderToken π r x ≠ secondToken π r x h
```

```lean
theorem momentInputs : Top.MomentsStatement →
    MonomialMoments ∧ ProductMomentCovariance ∧ (∀ j : IcoLetter, normSq (icoVector j) = 1)
```

```lean
theorem integratePassage_of_nodes : Top.MomentsStatement → Top.FiniteFactsStatement →
    PassageSiteMomentsStatement → PassageFubiniStatement → PassageNetworkPositiveStatement →
    PassageNextLowerBoundStatement →
    OriginalDegreeStatement → OriginalFactorStructureStatement → OriginalRawEvaluationStatement →
    MomentContractionStatement → MomentCovarianceTransferStatement → ContractionAffineStatement →
    Top.IntegratePassageStatement
```

```lean
theorem leaf_of_nodes : Top.MomentsStatement → Top.ThreeFactorMeanStatement →
    CoveredSlotEnumerationStatement → CornerMeanBoundsStatement → NormalizedMeanFactorStatement →
    Top.LeafStatement
```

```lean
theorem reducedStructure_of_nodes : Top.MomentsStatement → ReducedDegreeStatement →
    ReducedFactorStructureStatement → MomentCovarianceTransferStatement →
    ContractionAffineStatement → ContractionSupportStatement → DifferenceStructureStatement →
    ReducedStructureStatement
```

```lean
theorem simultaneousLeafReconstruction_of_nodes : PeripheralGeometryStatement → PeripheralFubiniStatement →
    PeripheralAssignmentStatement → SimultaneousLeafReconstructionStatement
```

```lean
theorem reduce_of_nodes : Top.MomentsStatement → Top.LeafStatement → ReducedDegreeStatement →
    MomentContractionStatement → SimultaneousLeafReconstructionStatement → ReducedStructureStatement →
    BallChordStatement → AffineEvaluationStatement → ProductBallNonnegativeStatement → Top.ReduceStatement
```

```lean
theorem inversion_of_nodes : BlochAlgebraStatement → BlochPositivityStatement →
    PauliExpansionStatement → PauliProductTraceStatement →
    InversionPolynomialStatement → ProductDensityPositiveStatement → TraceProductPositiveStatement →
    Top.InversionStatement
```

```lean
theorem retainedPairExpansion_of_nodes : MomentPauliInterchangeStatement →
    PairExpansionFromRealizationStatement → RetainedPairExpansionStatement
```

```lean
theorem operatorStructure_of_nodes : Top.MomentsStatement → ReducedDegreeStatement →
    ReducedStructureStatement → InversionPolynomialStatement →
    InversionCovarianceStatement → PauliHermitianStatement → ReflectionParityStatement →
    PauliRealityStatement → AdjointPauliCoordinatesStatement → AdjointPauliOrthogonalStatement →
    PauliRotationTransferStatement → CayleyTensorCommutationStatement → TensorLinearCoefficientStatement →
    SpinGeneratorTransferStatement → RetainedPairExpansionStatement → UnitPairSupportStatement →
    EqualPairExchangeStatement → PairExpansionTransferStatement →
    Top.OperatorStructureStatement
```

```lean
theorem sector_of_nodes : SectorSpinStableStatement → SectorWeightBasisStatement →
    SpanWeightLatticeStatement → SpinAdjointStatement → SpinCommutatorStatement →
    WeightLadderTransferStatement → CommonWeightEigenvectorStatement → LadderWalkStatement →
    PositiveSpectrumStatement → Top.SectorStatement
```

```lean
theorem gramResidual : Top.GramResidualStatement
```

```lean
theorem thresholdSymmetry_of_integerCheck : Top.IntegerCheckStatement → ThresholdSymmetryStatement
```

```lean
theorem h1Theorem_of_certificate : Top.CertificateStatement → H1FiniteDataStatementV2 →
    Top.H1TheoremStatement
```

```lean
theorem h1Theorem_of_parts : Top.IntegerCheckStatement → Top.CertificateStatement →
    H1FiniteDataStatementV2 → Top.H1TheoremStatement
```

```lean
theorem h1_of_theorem : Top.H1TheoremStatement → Top.H1Statement
```

```lean
theorem h1_of_parts : Top.IntegerCheckStatement → Top.CertificateStatement →
    H1FiniteDataStatementV2 → Top.H1Statement
```

```lean
theorem h1_of_certificateV2 : CertificateStatementV2 → Top.H1Statement
```

```lean
theorem passageSubtraction : PassageSubtractionStatement
```

```lean
theorem activeStatuses : ActiveStatusesStatement
```

```lean
theorem singlePauliTrace : SinglePauliTraceStatement
```

```lean
theorem inversionBall : InversionBallStatement
```

```lean
theorem differenceEvaluation : DifferenceEvaluationStatement
```

```lean
theorem reducedStatuses (π : PatternData) (r : Representation) (next : Bool)
    (x : Plane) (hx : x ∈ reducedSpinSites π r) :
    nextStatus π next x = .U ∨ nextStatus π next x = .D
```

```lean
theorem centralWeightHalf : CentralWeightHalfStatement
```

```lean
theorem pairTokensDistinct : PairTokensDistinctStatement
```
