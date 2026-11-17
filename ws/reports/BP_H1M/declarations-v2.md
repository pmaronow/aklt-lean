# V2 exact declarations

Namespace for H1-local declarations: `AKLT.Blueprint.H1`. Definitions and open leaves are not asserted as facts.

```lean
def PauliExpansionStatementV2 : Prop :=
  ∀ n : ℕ, ∀ J : Finset (Fin n), ∀ p : RealVectorPolynomial n,
    VectorAffineReal p → SupportedVectorsReal J p → ∀ u : Fin n → Vec3,
      evaluateRealPolynomial p u =
        ∑ a : J → Fin 4, p.coeff (pauliExponentReal J a) *
          ∏ j : J, pauliCoordinate (u j.val) (a j)
```

```lean
def PauliProductTraceStatementV2 : Prop :=
  (∀ a : Fin 4, ∀ u : Vec3, (pauli a * spinDensity u).trace = (pauliCoordinate u a : ℂ)) →
  ∀ n : ℕ, ∀ J : Finset (Fin n), ∀ p : RealVectorPolynomial n, ∀ u : Fin n → Vec3,
    (pauliOperatorReal J p * productDensityReal J u).trace =
      ((∑ a : J → Fin 4, p.coeff (pauliExponentReal J a) *
        ∏ j : J, pauliCoordinate (u j.val) (a j) : ℝ) : ℂ)
```

```lean
def InversionPolynomialStatementV2 : Prop :=
  ∀ n : ℕ, ∀ J I : Finset (Fin n), ∀ p : RealVectorPolynomial n,
    VectorAffineReal p → SupportedVectorsReal J p →
      VectorAffineReal (invertPolynomialReal I p) ∧ SupportedVectorsReal J (invertPolynomialReal I p) ∧
      ∀ u : Fin n → Vec3,
        evaluateRealPolynomial (invertPolynomialReal I p) (invertVectorsReal I u) = evaluateRealPolynomial p u
```

```lean
def ProductDensityPositiveStatementV2 : Prop :=
  ∀ n : ℕ, ∀ J : Finset (Fin n), ∀ u : Fin n → Vec3,
    (∀ j ∈ J, (spinDensity (u j)).PosSemidef) → (productDensityReal J u).PosSemidef
```

```lean
def InversionBallStatementV2 : Prop :=
  ∀ n : ℕ, ∀ I : Finset (Fin n), ∀ u : Fin n → Vec3, ∀ j : Fin n,
    normSq (invertVectorsReal I u j) = normSq (u j)
```

```lean
def RationalEmbeddingStructureStatementV2 : Prop :=
  ∀ p : VectorPolynomial, ∀ J : Finset (Fin 20),
    VectorAffine p → SupportedVectors J p →
      VectorAffineReal (MvPolynomial.map (Rat.castHom ℝ) p) ∧
      SupportedVectorsReal J (MvPolynomial.map (Rat.castHom ℝ) p)
```

```lean
def RationalEmbeddingEvaluationStatementV2 : Prop :=
  ∀ p : VectorPolynomial, ∀ u : Fin 20 → Vec3,
    evaluateRealPolynomial (MvPolynomial.map (Rat.castHom ℝ) p) u = evaluateReduced p u
```

```lean
def DifferenceStructureStatementV2 : Prop :=
  ∀ J : Finset (Fin 20), ∀ p q : RealVectorPolynomial 20, ∀ c : ℝ,
    VectorAffineReal p → VectorAffineReal q → OrthogonalInvariantV2 p → OrthogonalInvariantV2 q →
    SupportedVectorsReal J p → SupportedVectorsReal J q →
      VectorAffineReal (p - MvPolynomial.C c * q) ∧
      OrthogonalInvariantV2 (p - MvPolynomial.C c * q) ∧
      SupportedVectorsReal J (p - MvPolynomial.C c * q)
```

```lean
def DifferenceEvaluationStatementV2 : Prop :=
  ∀ π : PatternData, ∀ r : Representation, ∀ c : ℝ, ∀ u : Fin 20 → Vec3,
    evaluateRealPolynomial (reducedDifferenceReal π r c) u =
      evaluateReduced (reducedPolynomial π r false) u -
        c * evaluateReduced (reducedPolynomial π r true) u
```

```lean
def AffineEvaluationStatementV2 : Prop :=
  ∀ p : RealVectorPolynomial 20, VectorAffineReal p → SeparatelyAffine (evaluateRealPolynomial p)
```

```lean
def RationalPartitionsStructureStatementV2 : Prop :=
  ∀ π : PatternData, π.Covered → ∀ r : Representation, ∀ next : Bool,
    VectorAffine (reducedPolynomial π r next) ∧ OrthogonalInvariant (reducedPolynomial π r next) ∧
      SupportedVectors (reductionVectors π r) (reducedPolynomial π r next)
```

```lean
def ReducedStructureStatementV2 : Prop :=
  ∀ π : PatternData, π.Covered → ∀ r : Representation, ∀ c : ℝ,
    VectorAffineReal (reducedDifferenceReal π r c) ∧ OrthogonalInvariantV2 (reducedDifferenceReal π r c) ∧
      SupportedVectorsReal (reductionVectors π r) (reducedDifferenceReal π r c)
```

```lean
def RealDifferencePauliInterpolationStatementV2 : Prop :=
  ∀ π : PatternData, ∀ r : Representation, ∀ I : Finset (Fin 20), ∀ c : ℝ,
    pauliOperatorReal (reductionVectors π r) (invertPolynomialReal I (reducedDifferenceReal π r c)) =
      ((2 - 3 * c : ℝ) : ℂ) •
        pauliOperator (reductionVectors π r) (invertPolynomial I (reducedDifference π r (1 / 3))) +
      ((3 * c - 1 : ℝ) : ℂ) •
        pauliOperator (reductionVectors π r) (invertPolynomial I (reducedDifference π r (2 / 3)))
```

```lean
def OperatorStructureLinearCombinationStatementV2 : Prop :=
  ∀ π : PatternData, ∀ r : Representation,
    ∀ A B : Matrix (reductionVectors π r → Fin 2) (reductionVectors π r → Fin 2) ℂ,
      OperatorStructureAtV2 π r A → OperatorStructureAtV2 π r B → ∀ a b : ℝ,
        OperatorStructureAtV2 π r ((a : ℂ) • A + (b : ℂ) • B)
```

```lean
def H1FiniteDataStatementV2 : Prop :=
  ∀ π : PatternData, π.Covered → ∃ r : Representation, ∃ I : Finset (Fin 20),
    GroupInversion π r I ∧ ∃ D₀ : ℕ, ClearsDenominator π r D₀ ∧
      H1SectorWitnesses π r I D₀ (h1Numerator π) (h1Denominator π)
```

```lean
theorem rationalPartitionsStructure_of_nodesV2 : Top.MomentsStatement → ReducedDegreeStatement →
    ReducedFactorStructureStatement → MomentCovarianceTransferStatement → ContractionAffineStatement →
    ContractionSupportStatement → RationalPartitionsStructureStatementV2
```

```lean
theorem reducedStructure_of_nodesV2 : RationalPartitionsStructureStatementV2 →
    RationalEmbeddingStructureStatementV2 → RationalEmbeddingEvaluationStatementV2 →
    DifferenceStructureStatementV2 → ReducedStructureStatementV2
```

```lean
theorem reduce_of_nodesV2 : Top.MomentsStatement → Top.LeafStatement → ReducedDegreeStatement →
    MomentContractionStatement → SimultaneousLeafReconstructionStatement → ReducedStructureStatementV2 →
    BallChordStatement → AffineEvaluationStatementV2 → ProductBallNonnegativeStatement →
    DifferenceEvaluationStatementV2 → Top.ReduceStatementV2
```

```lean
theorem inversion_of_nodesV2 : BlochAlgebraStatement → BlochPositivityStatement →
    PauliExpansionStatementV2 → PauliProductTraceStatementV2 → InversionPolynomialStatementV2 →
    ProductDensityPositiveStatementV2 → InversionBallStatementV2 → TraceProductPositiveStatement →
    Top.InversionStatementV2
```

```lean
theorem operatorStructure_of_legacyV2 : Top.OperatorStructureStatement →
    RealDifferencePauliInterpolationStatementV2 → OperatorStructureLinearCombinationStatementV2 →
    Top.OperatorStructureStatementV2
```

```lean
theorem h1Theorem_of_shared_partsV2 : Top.IntegerCheckStatement → Top.CertificateStatement →
    Top.H1FiniteDataStatementV2 → Top.H1TheoremStatement
```

```lean
theorem h1_of_shared_partsV2 : Top.IntegerCheckStatement → Top.CertificateStatement →
    Top.H1FiniteDataStatementV2 → Top.H1Statement
```

```lean
theorem h1_of_shared_certificateV2 : Top.CertificateStatementV2 → Top.H1Statement
```

```lean
theorem inputs_of_shared_partsV2 : Top.CertificateStatementV2 → OtherInputPartsV2 →
    Top.InputsStatementV2
```

```lean
theorem main_of_shared_partsV2 : Top.CertificateStatementV2 → OtherInputPartsV2 →
    Top.RecStatement → Top.CutMOSStatement → Top.MainWStatement → Top.TorusKernelStatement →
    AKLT.Challenge.MainStatementV2
```

```lean
theorem integratePassage_of_nodesV2 : Top.MomentsStatement → Top.FiniteFactsStatement →
    PassageSiteMomentsStatement → PassageFubiniStatement → PassageNetworkPositiveStatement →
    PassageNextLowerBoundStatement →
    OriginalDegreeStatement → OriginalFactorStructureStatement → OriginalRawEvaluationStatement →
    MomentContractionStatement → MomentCovarianceTransferStatement → ContractionAffineStatement →
    Top.IntegratePassageStatement
```

```lean
theorem leaf_of_nodesV2 : Top.MomentsStatement → Top.ThreeFactorMeanStatement →
    CoveredSlotEnumerationStatement → CornerMeanBoundsStatement → NormalizedMeanFactorStatement →
    Top.LeafStatement
```

```lean
theorem sector_of_nodesV2 : SectorSpinStableStatement → SectorWeightBasisStatement →
    SpanWeightLatticeStatement → SpinAdjointStatement → SpinCommutatorStatement →
    WeightLadderTransferStatement → CommonWeightEigenvectorStatement → LadderWalkStatement →
    PositiveSpectrumStatement → Top.SectorStatement
```

```lean
theorem gramResidualV2 : Top.GramResidualStatement
```

```lean
theorem operatorStructure_of_nodesV2 : Top.MomentsStatement → ReducedDegreeStatement →
    ReducedStructureStatement → InversionPolynomialStatement →
    InversionCovarianceStatement → PauliHermitianStatement → ReflectionParityStatement →
    PauliRealityStatement → AdjointPauliCoordinatesStatement → AdjointPauliOrthogonalStatement →
    PauliRotationTransferStatement → CayleyTensorCommutationStatement → TensorLinearCoefficientStatement →
    SpinGeneratorTransferStatement → RetainedPairExpansionStatement → UnitPairSupportStatement →
    EqualPairExchangeStatement → PairExpansionTransferStatement →
    RealDifferencePauliInterpolationStatementV2 → OperatorStructureLinearCombinationStatementV2 →
    Top.OperatorStructureStatementV2
```
