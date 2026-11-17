module
public import AKLT.Blueprint.H1.NodesV2Handoff
public import AKLT.Blueprint.Top.Assembly

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-! Additive assemblies for the repaired paper-facing contracts. No leaf proof
is added: new mathematical compatibility facts remain explicit closed inputs. -/

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs

namespace AKLT.Blueprint.H1

/-- Extract the two exact rational partitions using the unchanged moment leaves. -/
theorem rationalPartitionsStructure_of_nodesV2 : Top.MomentsStatement → ReducedDegreeStatement →
    ReducedFactorStructureStatement → MomentCovarianceTransferStatement → ContractionAffineStatement →
    ContractionSupportStatement → RationalPartitionsStructureStatementV2 := by
  intro hMom hDegree hFactors hCov hAffine hSupport π hπ r next
  obtain ⟨hMonomial, hCovariance, _⟩ := momentInputs hMom
  obtain ⟨ha, hi, hs⟩ := hFactors π hπ r next
  exact ⟨hAffine _ _ _ ha,
    hCov hMonomial hCovariance _ _ (reducedStatuses π r next) _ (hDegree π hπ r next) hi,
    hSupport _ _ _ _ hs⟩

/-- Real scalar combinations follow coefficient embedding, never approximation
of a real threshold by a rational threshold. -/
theorem reducedStructure_of_nodesV2 : RationalPartitionsStructureStatementV2 →
    RationalEmbeddingStructureStatementV2 → RationalEmbeddingEvaluationStatementV2 →
    DifferenceStructureStatementV2 → ReducedStructureStatementV2 := by
  intro hPartitions hEmbed hEvaluate hDifference π hπ r c
  have hPoly (next : Bool) : VectorAffineReal (reducedPolynomialReal π r next) ∧
      OrthogonalInvariantV2 (reducedPolynomialReal π r next) ∧
      SupportedVectorsReal (reductionVectors π r) (reducedPolynomialReal π r next) := by
    obtain ⟨ha, hi, hs⟩ := hPartitions π hπ r next
    obtain ⟨hea, hes⟩ := hEmbed _ _ ha hs
    refine ⟨hea, ?_, hes⟩
    intro R hR u
    change evaluateRealPolynomial (MvPolynomial.map (Rat.castHom ℝ) _) _ =
      evaluateRealPolynomial (MvPolynomial.map (Rat.castHom ℝ) _) _
    rw [hEvaluate, hEvaluate]
    exact hi R hR u
  exact hDifference _ _ _ c (hPoly false).1 (hPoly true).1
    (hPoly false).2.1 (hPoly true).2.1 (hPoly false).2.2 (hPoly true).2.2

/-- `c:reduce`, repaired real-threshold scope, with unchanged common K and u. -/
theorem reduce_of_nodesV2 : Top.MomentsStatement → Top.LeafStatement → ReducedDegreeStatement →
    MomentContractionStatement → SimultaneousLeafReconstructionStatement → ReducedStructureStatementV2 →
    BallChordStatement → AffineEvaluationStatementV2 → ProductBallNonnegativeStatement →
    DifferenceEvaluationStatementV2 → Top.ReduceStatementV2 := by
  intro hMom hLeaf hDegree hContract hReconstruct hStructure hChord hAffine hBall hEvaluate π hπ r c _ _
  have hMonomial := (momentInputs hMom).1
  have hExact (next : Bool) (u : Fin 20 → Vec3) :
      evaluateReduced (reducedPolynomial π r next) u =
        rawFunctional (reducedSpinSites π r) (nextStatus π next) (reducedIntegrand π r next) u :=
    hContract hMonomial _ _ (reducedStatuses π r next) _ (hDegree π hπ r next) u
  have hRec (m : Fin 20 → UnitVector) :=
    hReconstruct (momentInputs hMom).2.2 π hπ r hExact m (hLeaf π hπ m)
  obtain ⟨ha, hi, _⟩ := hStructure π hπ r c
  refine ⟨ha, hi, ?_, ?_⟩
  · intro hUnit m
    obtain ⟨K, hK, u, hu, hCur, hNext⟩ := hRec m
    have hNonneg := hBall hChord _ (hAffine _ ha) hUnit u hu
    have he := hEvaluate π r c u
    rw [hCur, hNext]
    nlinarith [mul_nonneg hK.le hNonneg]
  · intro m
    obtain ⟨K, hK, u, hu, hCur, hNext⟩ := hRec m
    exact ⟨K, hK, u, fun j _ => hu j, hCur, hNext⟩

/-- `l:inversion`, arbitrary finite n and genuinely real coefficients. The
one-spin algebra and unrestricted finite-index PSD trace bound are unchanged. -/
theorem inversion_of_nodesV2 : BlochAlgebraStatement → BlochPositivityStatement →
    PauliExpansionStatementV2 → PauliProductTraceStatementV2 → InversionPolynomialStatementV2 →
    ProductDensityPositiveStatementV2 → InversionBallStatementV2 → TraceProductPositiveStatement →
    Top.InversionStatementV2 := by
  intro hAlgebra hPositive hExpansion hTrace hInvert hProduct hBall hTracePositive
  have hDensity (u : Vec3) (hu : normSq u ≤ 1) :
      (spinDensity u).PosSemidef ∧ (spinDensity u).trace = 1 := by
    obtain ⟨hH, hSquare, hTr⟩ := hAlgebra u
    have hNorm : 0 ≤ normSq u := by
      change 0 ≤ ∑ i : Fin 3, u i * u i
      exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (u i))
    refine ⟨hPositive _ hH _ hNorm hu hSquare, ?_⟩
    change (((1 / 2 : ℂ) • (1 + blochMatrix u))).trace = 1
    simp [Matrix.trace_smul, Matrix.trace_add, hTr]
  have hTraceFormula (n : ℕ) (J : Finset (Fin n)) (p : RealVectorPolynomial n)
      (ha : VectorAffineReal p) (hs : SupportedVectorsReal J p) (u : Fin n → Vec3) :
      (evaluateRealPolynomial p u : ℂ) = (pauliOperatorReal J p * productDensityReal J u).trace := by
    rw [hTrace singlePauliTrace]
    exact congrArg (fun x : ℝ => (x : ℂ)) (hExpansion n J p ha hs u)
  refine ⟨hDensity, ?_⟩
  intro n J p ha hs I _
  obtain ⟨hia, his, hEval⟩ := hInvert n J I p ha hs
  have hIdentity (u : Fin n → Vec3) : (evaluateRealPolynomial p u : ℂ) =
      (pauliOperatorReal J (invertPolynomialReal I p) * productDensityReal J (invertVectorsReal I u)).trace := by
    rw [← hEval u]
    exact hTraceFormula n J _ hia his _
  refine ⟨fun u _ => hIdentity u, ?_⟩
  intro hOperator u hu
  have hProductDensity := hProduct n J (invertVectorsReal I u) (fun j hj =>
    (hDensity _ (by rw [hBall]; exact hu j hj)).1)
  have hNonneg := hTracePositive (J → Fin 2) _ _ hOperator hProductDensity
  rw [← hIdentity u] at hNonneg
  exact hNonneg

/-- `l:Ostruct`, real thresholds, from two legacy rational structural instances.
The interpolation weights may be negative: only linear identities are transferred. -/
theorem operatorStructure_of_legacyV2 : Top.OperatorStructureStatement →
    RealDifferencePauliInterpolationStatementV2 → OperatorStructureLinearCombinationStatementV2 →
    Top.OperatorStructureStatementV2 := by
  intro hLegacy hInterpolation hLinear π hπ r I hI c _ _
  have hA : OperatorStructureAtV2 π r (pauliOperator (reductionVectors π r)
      (invertPolynomial I (reducedDifference π r (1 / 3)))) :=
    hLegacy π hπ r I hI (1 / 3) (by norm_num) (by norm_num)
  have hB : OperatorStructureAtV2 π r (pauliOperator (reductionVectors π r)
      (invertPolynomial I (reducedDifference π r (2 / 3)))) :=
    hLegacy π hπ r I hI (2 / 3) (by norm_num) (by norm_num)
  change OperatorStructureAtV2 π r (pauliOperatorReal (reductionVectors π r)
    (invertPolynomialReal I (reducedDifferenceReal π r c)))
  rw [hInterpolation]
  exact hLinear π r _ _ hA hB (2 - 3 * c) (3 * c - 1)

/-- The data owner now supplies the repaired shared contract, whose witness
predicate and thresholds are definitionally the same as the frozen local ones. -/
theorem h1Theorem_of_shared_partsV2 : Top.IntegerCheckStatement → Top.CertificateStatement →
    Top.H1FiniteDataStatementV2 → Top.H1TheoremStatement := by
  intro hInteger hCertificate hData
  exact h1Theorem_of_parts hInteger hCertificate hData

theorem h1_of_shared_partsV2 : Top.IntegerCheckStatement → Top.CertificateStatement →
    Top.H1FiniteDataStatementV2 → Top.H1Statement := by
  intro hInteger hCertificate hData
  exact h1_of_parts hInteger hCertificate hData

theorem h1_of_shared_certificateV2 : Top.CertificateStatementV2 → Top.H1Statement := by
  intro hCertificate
  exact h1_of_theorem (h1Theorem_of_certificate hCertificate.1 hCertificate.2)

/-- Supply exactly the repaired global input package, retaining the shared
finite-data check and both archive/corrected-stationary obligations. -/
theorem inputs_of_shared_partsV2 : Top.CertificateStatementV2 → OtherInputPartsV2 →
    Top.InputsStatementV2 := by
  rintro hCertificate ⟨hH2, hH3, hRate, hCeiling, hAutomaton, hStationary⟩
  exact ⟨⟨h1_of_shared_certificateV2 hCertificate, hH2, hH3, hRate, hCeiling⟩,
    hCertificate.2, hAutomaton, hStationary⟩

/-- Optional orchestrator bridge to the repaired top assembly; every other
lane's mathematical input stays explicit and no numeric dataset is certified. -/
theorem main_of_shared_partsV2 : Top.CertificateStatementV2 → OtherInputPartsV2 →
    Top.RecStatement → Top.CutMOSStatement → Top.MainWStatement → Top.TorusKernelStatement →
    AKLT.Challenge.MainStatementV2 := by
  intro hCertificate hOther hRec hCut hMainW hKernel
  exact Top.mainV2_of_partsV2 (inputs_of_shared_partsV2 hCertificate hOther) hRec hCut hMainW hKernel

/-- Reuse the unchanged target and the frozen assembly at the repaired layer. -/
theorem integratePassage_of_nodesV2 : Top.MomentsStatement → Top.FiniteFactsStatement →
    PassageSiteMomentsStatement → PassageFubiniStatement → PassageNetworkPositiveStatement →
    PassageNextLowerBoundStatement →
    OriginalDegreeStatement → OriginalFactorStructureStatement → OriginalRawEvaluationStatement →
    MomentContractionStatement → MomentCovarianceTransferStatement → ContractionAffineStatement →
    Top.IntegratePassageStatement := integratePassage_of_nodes

/-- Reuse the unchanged target and the frozen assembly at the repaired layer. -/
theorem leaf_of_nodesV2 : Top.MomentsStatement → Top.ThreeFactorMeanStatement →
    CoveredSlotEnumerationStatement → CornerMeanBoundsStatement → NormalizedMeanFactorStatement →
    Top.LeafStatement := leaf_of_nodes

/-- Reuse the unchanged target and the frozen assembly at the repaired layer. -/
theorem sector_of_nodesV2 : SectorSpinStableStatement → SectorWeightBasisStatement →
    SpanWeightLatticeStatement → SpinAdjointStatement → SpinCommutatorStatement →
    WeightLadderTransferStatement → CommonWeightEigenvectorStatement → LadderWalkStatement →
    PositiveSpectrumStatement → Top.SectorStatement := sector_of_nodes

/-- Reuse the already proved Gram/residual target unchanged. -/
theorem gramResidualV2 : Top.GramResidualStatement := gramResidual

/-- Full leaf-facing real structural assembly: the rational structural assembly is reused internally. -/
theorem operatorStructure_of_nodesV2 : Top.MomentsStatement → ReducedDegreeStatement →
    ReducedStructureStatement → InversionPolynomialStatement →
    InversionCovarianceStatement → PauliHermitianStatement → ReflectionParityStatement →
    PauliRealityStatement → AdjointPauliCoordinatesStatement → AdjointPauliOrthogonalStatement →
    PauliRotationTransferStatement → CayleyTensorCommutationStatement → TensorLinearCoefficientStatement →
    SpinGeneratorTransferStatement → RetainedPairExpansionStatement → UnitPairSupportStatement →
    EqualPairExchangeStatement → PairExpansionTransferStatement →
    RealDifferencePauliInterpolationStatementV2 → OperatorStructureLinearCombinationStatementV2 →
    Top.OperatorStructureStatementV2 := by
  intro hMom hDegree hStructure hInvert hCov hHermitian hParity hReal hCoordinates hOrthogonal hRotate hCayley hCoefficient hGenerator hExpansion hUnitPair hExchange hPairTransfer hInterpolation hLinear
  exact operatorStructure_of_legacyV2 (operatorStructure_of_nodes hMom hDegree hStructure hInvert hCov hHermitian hParity hReal hCoordinates hOrthogonal hRotate hCayley hCoefficient hGenerator hExpansion hUnitPair hExchange hPairTransfer)
    hInterpolation hLinear

end AKLT.Blueprint.H1
