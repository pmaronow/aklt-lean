import AKLT.Blueprint.H1.NodesCertificate

/-! Kernel-checked implications assembling Appendix D. Every mathematical input
at an assembly boundary is a closed Prop. No open node has been asserted as a fact. -/

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs

namespace AKLT.Blueprint.H1

/-- Extract the three parts of the shared moment interface used here. -/
theorem momentInputs : Top.MomentsStatement →
    MonomialMoments ∧ ProductMomentCovariance ∧ (∀ j : IcoLetter, normSq (icoVector j) = 1) := by
  rintro ⟨_, hUnit, _, _, _, _, _, _, hMonomial, hCovariance⟩
  exact ⟨hMonomial, hCovariance, hUnit⟩

/-- `l:Iw`: original contraction, passage Fubini, and strict positivity. -/
theorem integratePassage_of_nodes : Top.MomentsStatement → Top.FiniteFactsStatement →
    PassageSiteMomentsStatement → PassageFubiniStatement → PassageNetworkPositiveStatement →
    PassageNextLowerBoundStatement →
    OriginalDegreeStatement → OriginalFactorStructureStatement → OriginalRawEvaluationStatement →
    MomentContractionStatement → MomentCovarianceTransferStatement → ContractionAffineStatement →
    Top.IntegratePassageStatement := by
  intro hMom hFinite hSite hFubini hPositive hLower hDegree hFactors hRaw hContract hCov hAffine
  obtain ⟨hMonomial, hCovariance, hUnit⟩ := momentInputs hMom
  intro π hπ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro next
    exact hAffine π.active (nextStatus π next) (originalIntegrand π next) (hFactors π next).1
  · intro next m
    exact (hContract hMonomial π.active (nextStatus π next) (activeStatuses π next)
      (originalIntegrand π next) (hDegree π hπ next) (fun j => (m j).val)).trans (hRaw π next m)
  · intro next
    exact hCov hMonomial hCovariance π.active (nextStatus π next) (activeStatuses π next)
      (originalIntegrand π next) (hDegree π hπ next) (hFactors π next).2
  · intro m f g hSet hof hog hfg
    obtain ⟨hCurrent, hNext⟩ := hFubini (hSite hMonomial) π hπ m f g ⟨hSet, hof, hog, hfg⟩
    have hNetwork := hPositive (fun n D hD => (hFinite.2 n D hD).1) π hπ m
    have hLowerNext := hLower hUnit π hπ m f g
    refine ⟨hCurrent, hNext, ?_, ?_⟩
    · rw [hNext]
      linarith
    · intro c _ _
      rw [hCurrent, hNext, passageSubtraction]
      congr 1
      funext n
      dsimp [passageI, passageJ]
      ring

/-- `l:leaf`: the isolated and one-bond assertions share the same site data. -/
theorem leaf_of_nodes : Top.MomentsStatement → Top.ThreeFactorMeanStatement →
    CoveredSlotEnumerationStatement → CornerMeanBoundsStatement → NormalizedMeanFactorStatement →
    Top.LeafStatement := by
  intro hMom hMean hSlots hCorner hFactor π hπ m x hx hX
  have hMonomial := (momentInputs hMom).1
  have hData : 0 < siteFunctional (π.statusAt x) (coveredSiteField m x) ∧
      ∃ A : ℝ, 0 < A ∧ ∃ u : Vec3, normSq u ≤ 1 ∧
        ∀ v : Vec3, normSq v ≤ 1 →
          siteFunctional (π.statusAt x) (fun n => coveredSiteField m x n * (1 + dot n v)) =
            A * (1 + (replacementRadius π x : ℝ) * dot u v) := by
    rcases hSlots π hπ m x hx hX with ⟨a, hs, hρ, hField⟩ | ⟨a, hs, hρ, hField⟩
    · obtain ⟨hA, hBound⟩ := hMean.1 3 (by omega) (fun j => (a j).val)
        (fun j => (a j).property.le) .U (Or.inl rfl)
      refine ⟨by simpa [hs, hField] using hA, ?_⟩
      simpa [hs, hField, hρ] using
        hFactor 3 (fun j => (a j).val) .U (3 / 5) (by norm_num) hA hBound
    · obtain ⟨hA, hBound⟩ := hCorner hMonomial a (π.statusAt x) hs
      have hρR : (replacementRadius π x : ℝ) =
          if π.statusAt x = .U then (1 / 2 : ℝ) else 1 / 3 := by
        rw [hρ]
        split <;> norm_num
      have hρPos : 0 < (if π.statusAt x = .U then (1 / 2 : ℝ) else 1 / 3) := by
        split <;> norm_num
      refine ⟨by simpa [hField] using hA, ?_⟩
      simpa only [hField, hρR] using
        hFactor 2 (fun j => (a j).val) (π.statusAt x) _ hρPos hA hBound
  exact ⟨fun _ => hData.1, fun _ => hData.2⟩

/-- `c:reduce`: the shared contraction nodes establish all polynomial structure. -/
theorem reducedStructure_of_nodes : Top.MomentsStatement → ReducedDegreeStatement →
    ReducedFactorStructureStatement → MomentCovarianceTransferStatement →
    ContractionAffineStatement → ContractionSupportStatement → DifferenceStructureStatement →
    ReducedStructureStatement := by
  intro hMom hDegree hFactors hCov hAffine hSupport hDifference π hπ r c
  obtain ⟨hMonomial, hCovariance, _⟩ := momentInputs hMom
  have hPoly (next : Bool) : VectorAffine (reducedPolynomial π r next) ∧
      OrthogonalInvariant (reducedPolynomial π r next) ∧
      SupportedVectors (reductionVectors π r) (reducedPolynomial π r next) := by
    obtain ⟨ha, hi, hs⟩ := hFactors π hπ r next
    exact ⟨hAffine _ _ _ ha,
      hCov hMonomial hCovariance _ _ (reducedStatuses π r next) _ (hDegree π hπ r next) hi,
      hSupport _ _ _ _ hs⟩
  exact hDifference _ _ _ c (hPoly false).1 (hPoly true).1
    (hPoly false).2.1 (hPoly true).2.1 (hPoly false).2.2 (hPoly true).2.2

/-- `c:reduce`: compose the geometric split, finite Fubini and one common
assignment, then replace the raw functionals by their rational contractions. -/
theorem simultaneousLeafReconstruction_of_nodes : PeripheralGeometryStatement → PeripheralFubiniStatement →
    PeripheralAssignmentStatement → SimultaneousLeafReconstructionStatement := by
  intro hGeometry hFubini hAssignment hUnit π hπ r hExact m hRule
  obtain ⟨K, hK, u, hu, hSeparated⟩ := hAssignment hUnit π hπ r (hGeometry π hπ r) m hRule
  refine ⟨K, hK, u, hu, ?_, ?_⟩
  · simpa only [Bool.false_eq_true, ite_false] using
      (hFubini π hπ r (hGeometry π hπ r) false m).trans
        ((hSeparated false).trans (congrArg (fun x : ℝ => K * x) (hExact false u).symm))
  · simpa only [ite_true] using
      (hFubini π hπ r (hGeometry π hπ r) true m).trans
        ((hSeparated true).trans (congrArg (fun x : ℝ => K * x) (hExact true u).symm))

/-- `c:reduce`: common positive reconstruction and successive convex chords. -/
theorem reduce_of_nodes : Top.MomentsStatement → Top.LeafStatement → ReducedDegreeStatement →
    MomentContractionStatement → SimultaneousLeafReconstructionStatement → ReducedStructureStatement →
    BallChordStatement → AffineEvaluationStatement → ProductBallNonnegativeStatement → Top.ReduceStatement := by
  intro hMom hLeaf hDegree hContract hReconstruct hStructure hChord hAffine hBall π hπ r c _ _
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
    have he := differenceEvaluation π r c u
    rw [hCur, hNext]
    nlinarith [mul_nonneg hK.le hNonneg]
  · intro m
    obtain ⟨K, hK, u, hu, hCur, hNext⟩ := hRec m
    exact ⟨K, hK, u, fun j _ => hu j, hCur, hNext⟩

/-- `l:inversion`: density positivity, exact trace identity, and the PSD trace bound. -/
theorem inversion_of_nodes : BlochAlgebraStatement → BlochPositivityStatement →
    PauliExpansionStatement → PauliProductTraceStatement →
    InversionPolynomialStatement → ProductDensityPositiveStatement → TraceProductPositiveStatement →
    Top.InversionStatement := by
  intro hAlgebra hPositive hExpansion hTrace hInvert hProduct hTracePositive
  have hDensity (u : Vec3) (hu : normSq u ≤ 1) :
      (spinDensity u).PosSemidef ∧ (spinDensity u).trace = 1 := by
    obtain ⟨hH, hSquare, hTr⟩ := hAlgebra u
    have hNorm : 0 ≤ normSq u := by
      change 0 ≤ ∑ i : Fin 3, u i * u i
      exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (u i))
    refine ⟨hPositive _ hH _ hNorm hu hSquare, ?_⟩
    change (((1 / 2 : ℂ) • (1 + blochMatrix u))).trace = 1
    simp [Matrix.trace_smul, Matrix.trace_add, hTr]
  have hTraceFormula (J : Finset (Fin 20)) (p : VectorPolynomial)
      (ha : VectorAffine p) (hs : SupportedVectors J p) (u : Fin 20 → Vec3) :
      (evaluateReduced p u : ℂ) = (pauliOperator J p * productDensity J u).trace := by
    rw [hTrace singlePauliTrace]
    exact congrArg (fun x : ℝ => (x : ℂ)) (hExpansion J p ha hs u)
  refine ⟨hDensity, ?_⟩
  intro J p ha hs I _
  obtain ⟨hia, his, hEval⟩ := hInvert J I p ha hs
  have hIdentity (u : Fin 20 → Vec3) : (evaluateReduced p u : ℂ) =
      (pauliOperator J (invertPolynomial I p) * productDensity J (invertVectors I u)).trace := by
    rw [← hEval u]
    exact hTraceFormula J _ hia his _
  refine ⟨fun u _ => hIdentity u, ?_⟩
  intro hOperator u hu
  have hProductDensity := hProduct J (invertVectors I u) (fun j hj =>
    (hDensity _ (by rw [inversionBall]; exact hu j hj)).1)
  have hNonneg := hTracePositive (J → Fin 2) _ _ hOperator hProductDensity
  rw [← hIdentity u] at hNonneg
  exact hNonneg

/-- `l:Ostruct`: connect the generic moment/Pauli sum with the factored pair
realization. Degree and atom-norm inputs remain explicit mathematical premises. -/
theorem retainedPairExpansion_of_nodes : MomentPauliInterchangeStatement →
    PairExpansionFromRealizationStatement → RetainedPairExpansionStatement := by
  intro hInterchange hPair hMonomial hUnit π hπ r hDegree I hI c x hPairFlag
  exact hPair hUnit π hπ r I hI
    (fun next => hInterchange hMonomial _ _ (reducedStatuses π r next) _ (hDegree next) _ I)
    c x hPairFlag

/-- `l:Ostruct`: orthogonal covariance gives reality and SU(2) commutation;
coefficient comparison gives generators; finite equal-pair sums give support. -/
theorem operatorStructure_of_nodes : Top.MomentsStatement → ReducedDegreeStatement →
    ReducedStructureStatement → InversionPolynomialStatement →
    InversionCovarianceStatement → PauliHermitianStatement → ReflectionParityStatement →
    PauliRealityStatement → AdjointPauliCoordinatesStatement → AdjointPauliOrthogonalStatement →
    PauliRotationTransferStatement → CayleyTensorCommutationStatement → TensorLinearCoefficientStatement →
    SpinGeneratorTransferStatement → RetainedPairExpansionStatement → UnitPairSupportStatement →
    EqualPairExchangeStatement → PairExpansionTransferStatement →
    Top.OperatorStructureStatement := by
  intro hMom hDegree hStructure hInvert hCov hHermitian hParity hReal hCoordinates hOrthogonal hRotate
    hCayley hCoefficient hGenerator hExpansion hUnitPair hExchange hPairTransfer π hπ r I hI c _ _
  let J := reductionVectors π r
  let p := invertPolynomial I (reducedDifference π r c)
  obtain ⟨ha, hi, hs⟩ := hStructure π hπ r c
  obtain ⟨hia, his, _⟩ := hInvert J I (reducedDifference π r c) ha hs
  have hInvariant : OrthogonalInvariant p := hCov _ hi I
  have hSU2 : ∀ g : Matrix (Fin 2) (Fin 2) ℂ, g.conjTranspose * g = 1 → g.det = 1 →
      Commute (pauliOperator J p) (tensorPowerMatrix J g) := by
    intro g hU hDet
    obtain ⟨R, hR⟩ := hCoordinates g hU hDet
    exact hRotate J p hia his hInvariant g hU R (hOrthogonal g hU R hR) hR
  have hSpin := hGenerator J (pauliOperator J p) (fun k =>
    hCoefficient J (pauliOperator J p) _ (hCayley J (pauliOperator J p) hSU2 k))
  refine ⟨hHermitian J p, hReal J p (hParity J p hia his hInvariant), hSU2,
    hSpin.1, hSpin.2.1, hSpin.2.2, ?_⟩
  intro x hPair
  have hResult := hPairTransfer J (leaderToken π r x) (secondToken π r x hPair)
    (Matrix.toEuclideanLin (pauliOperator J p)) (π.statusAt x.val = .U)
    (hExpansion (momentInputs hMom).1 (momentInputs hMom).2.2 π hπ r (hDegree π hπ r) I hI c x hPair)
    (hUnitPair J _ _ (pairTokensDistinct π r x hPair)) (hExchange J _ _)
  exact ⟨hResult.1, fun _ => hResult.2⟩

/-- `l:sector`: every eigenvalue reaches the actual central eigenspace, and
strict quadratic-form positivity is detected by the same eigenvalue set. -/
theorem sector_of_nodes : SectorSpinStableStatement → SectorWeightBasisStatement →
    SpanWeightLatticeStatement → SpinAdjointStatement → SpinCommutatorStatement →
    WeightLadderTransferStatement → CommonWeightEigenvectorStatement → LadderWalkStatement →
    PositiveSpectrumStatement → Top.SectorStatement := by
  intro hStable hWeights hSpan hAdjoint hCommutator hTransfer hStart hWalk hSpectrum π r ε
  dsimp only
  intro O hPreserve hSymmetric hZ hPlus hMinus
  let J := reductionVectors π r
  let S := exchangeSpace π r ε
  let C := centralSpace π r ε
  have hCast (q : ℚ) : ((q : ℝ) : ℂ) = (q : ℂ) := by norm_cast
  have hPreserveC : ∀ ψ ∈ C, O ψ ∈ C := by
    intro ψ hψ
    refine ⟨hPreserve ψ hψ.1, ?_⟩
    apply Module.End.mem_eigenspace_iff.mpr
    rw [← hZ ψ hψ.1, Module.End.mem_eigenspace_iff.mp hψ.2, map_smul]
  have hEigenvalues : eigenvaluesOn C O = eigenvaluesOn S O := by
    apply Set.Subset.antisymm
    · rintro μ ⟨ψ, hψ, hNonzero, hEigen⟩
      exact ⟨ψ, hψ.1, hNonzero, hEigen⟩
    · intro μ hμ
      obtain ⟨v, hv, hNonzero, hEigen, m, hWeight⟩ :=
        hStart J S O hPreserve hSymmetric (hStable π r ε).1
          (fun ψ _ χ _ => (hAdjoint J ψ χ).1) hZ μ hμ
      have hLattice : ∃ z : ℤ, m = (centralWeight π r : ℝ) + z :=
        hSpan J (ExchangeBasis π r ε) (sectorVector π r ε)
          (fun b => (exchangeWeight π r ε b : ℝ)) (centralWeight π r : ℝ)
          (fun b => by simpa only [hCast] using (hWeights π r ε b).1)
          (fun b => (hWeights π r ε b).2) v hv hNonzero m hWeight
      obtain ⟨w, hw, hwNonzero, hwEigen, hwWeight⟩ :=
        hWalk J S (centralWeight π r : ℝ) (centralWeightHalf π r) (hStable π r ε)
          (hTransfer J (hAdjoint J) (hCommutator J)) O hPlus hMinus
          μ v hv hNonzero hEigen m hWeight hLattice
      refine ⟨w, ⟨hw, Module.End.mem_eigenspace_iff.mpr ?_⟩, hwNonzero, hwEigen⟩
      simpa only [hCast] using hwWeight
  refine ⟨hPreserveC, hEigenvalues, ?_⟩
  have hCentral := hSpectrum J C O hPreserveC
    (fun ψ hψ χ hχ => hSymmetric ψ hψ.1 χ hχ.1)
  have hSector := hSpectrum J S O hPreserve hSymmetric
  rw [hCentral, hSector, hEigenvalues]

/-- `l:gram-residual`: direct reuse of the generic integer theorem over R and C.
The library proves the stronger result without triangularity or invertibility. -/
theorem gramResidual : Top.GramResidualStatement := by
  intro n M L hM _ g d S hRows
  obtain ⟨hg, hd, hS, hRows⟩ := hRows
  have hdd : ∀ i, ∑ j ∈ Finset.univ.erase i,
      |(((d : ℤ) * (S : ℤ) ^ 2) • M - (g : ℤ) • (L * L.transpose)) i j| <
        (((d : ℤ) * (S : ℤ) ^ 2) • M - (g : ℤ) • (L * L.transpose)) i i :=
    fun i => (hRows i).2
  have hReal := AKLT.Gen.Gram.int_gram_residual_posDef (K := ℝ) hM
    (by exact_mod_cast hg) (by exact_mod_cast hd) (by exact_mod_cast hS) hdd
  have hComplex := AKLT.Gen.Gram.int_gram_residual_posDef (K := ℂ) hM
    (by exact_mod_cast hg) (by exact_mod_cast hd) (by exact_mod_cast hS) hdd
  exact ⟨hReal.1, hComplex.1, hReal.2, hComplex.2⟩

/-- `l:integercheck`: use the externally supplied reconstruction theorem,
without reproving any finite reconstruction or optional Bareiss facts. -/
theorem thresholdSymmetry_of_integerCheck : Top.IntegerCheckStatement → ThresholdSymmetryStatement := by
  intro hInteger π hπ r I hI D₀ hD₀ p q hp hq hpq ε
  have h := (hInteger.1 π hπ r I hI D₀ hD₀ p q hp hq hpq ε).1
  exact ((h false).1.smul (5 * (q : ℤ))).sub ((h true).1.smul (3 * (p : ℤ)))

/-- `t:H1`: finite data existence plus the externally owned certificate
soundness implication gives the pointwise theorem at the two exact thresholds. -/
theorem h1Theorem_of_certificate : Top.CertificateStatement → H1FiniteDataStatementV2 →
    Top.H1TheoremStatement := by
  intro hCertificate hData π hπ m
  obtain ⟨r, I, hI, D₀, hD₀, hWitness⟩ := hData π hπ
  have hp : 0 < h1Numerator π := by unfold h1Numerator; split <;> norm_num
  have hq : 0 < h1Denominator π := by unfold h1Denominator; split <;> norm_num
  have hpq : (h1Numerator π : ℚ) / h1Denominator π < 1 := by
    unfold h1Numerator h1Denominator
    split <;> norm_num
  have h := hCertificate π hπ r I hI D₀ hD₀ (h1Numerator π) (h1Denominator π) hp hq hpq hWitness m
  have hValue : (h1Numerator π : ℝ) / h1Denominator π =
      if π.outgoing = .north then (961 / 1000 : ℝ) else 187 / 200 := by
    unfold h1Numerator h1Denominator
    split <;> norm_num
  rw [hValue] at h
  linarith

/-- Compatibility assembly for the requested two Top inputs. IntegerCheck is
logically redundant here because the existing Certificate conclusion already
contains the complete pointwise inequality; actual data coverage is essential. -/
theorem h1Theorem_of_parts : Top.IntegerCheckStatement → Top.CertificateStatement →
    H1FiniteDataStatementV2 → Top.H1TheoremStatement := by
  intro _ hCertificate hData
  exact h1Theorem_of_certificate hCertificate hData

/-- `h:H1`: add the elementary interval checks for the fixed thresholds. -/
theorem h1_of_theorem : Top.H1TheoremStatement → Top.H1Statement := by
  intro h
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, h⟩

theorem h1_of_parts : Top.IntegerCheckStatement → Top.CertificateStatement →
    H1FiniteDataStatementV2 → Top.H1Statement := by
  intro hInteger hCertificate hData
  exact h1_of_theorem (h1Theorem_of_parts hInteger hCertificate hData)

theorem h1_of_certificateV2 : CertificateStatementV2 → Top.H1Statement := by
  intro h
  exact h1_of_theorem (h1Theorem_of_certificate h.1 h.2)

end AKLT.Blueprint.H1
