import AKLT.Blueprint.H1.All

/-! Type closure and proof-dependency audit of every exported theorem. -/

#check (AKLT.Blueprint.H1.H1FiniteDataStatementV2 : Prop)
#check (AKLT.Blueprint.H1.CertificateStatementV2 : Prop)
#check (AKLT.Blueprint.H1.ThresholdSymmetryStatement : Prop)
#check (AKLT.Blueprint.H1.CoveredSlotEnumerationStatement : Prop)
#check (AKLT.Blueprint.H1.CornerMeanBoundsStatement : Prop)
#check (AKLT.Blueprint.H1.NormalizedMeanFactorStatement : Prop)
#check (AKLT.Blueprint.H1.PassageSiteMomentsStatement : Prop)
#check (AKLT.Blueprint.H1.PassageFubiniStatement : Prop)
#check (AKLT.Blueprint.H1.PassageNetworkPositiveStatement : Prop)
#check (AKLT.Blueprint.H1.PassageNextLowerBoundStatement : Prop)
#check (AKLT.Blueprint.H1.PassageSubtractionStatement : Prop)
#check (AKLT.Blueprint.H1.OriginalDegreeStatement : Prop)
#check (AKLT.Blueprint.H1.OriginalFactorStructureStatement : Prop)
#check (AKLT.Blueprint.H1.OriginalRawEvaluationStatement : Prop)
#check (AKLT.Blueprint.H1.MomentContractionStatement : Prop)
#check (AKLT.Blueprint.H1.MomentCovarianceTransferStatement : Prop)
#check (AKLT.Blueprint.H1.ContractionAffineStatement : Prop)
#check (AKLT.Blueprint.H1.ContractionSupportStatement : Prop)
#check (AKLT.Blueprint.H1.ActiveStatusesStatement : Prop)
#check (AKLT.Blueprint.H1.BlochAlgebraStatement : Prop)
#check (AKLT.Blueprint.H1.BlochPositivityStatement : Prop)
#check (AKLT.Blueprint.H1.SinglePauliTraceStatement : Prop)
#check (AKLT.Blueprint.H1.PauliExpansionStatement : Prop)
#check (AKLT.Blueprint.H1.PauliProductTraceStatement : Prop)
#check (AKLT.Blueprint.H1.InversionPolynomialStatement : Prop)
#check (AKLT.Blueprint.H1.ProductDensityPositiveStatement : Prop)
#check (AKLT.Blueprint.H1.TraceProductPositiveStatement : Prop)
#check (AKLT.Blueprint.H1.InversionBallStatement : Prop)
#check (AKLT.Blueprint.H1.ReducedDegreeStatement : Prop)
#check (AKLT.Blueprint.H1.ReducedFactorStructureStatement : Prop)
#check (AKLT.Blueprint.H1.PeripheralGeometryStatement : Prop)
#check (AKLT.Blueprint.H1.PeripheralFubiniStatement : Prop)
#check (AKLT.Blueprint.H1.PeripheralAssignmentStatement : Prop)
#check (AKLT.Blueprint.H1.SimultaneousLeafReconstructionStatement : Prop)
#check (AKLT.Blueprint.H1.BallChordStatement : Prop)
#check (AKLT.Blueprint.H1.AffineEvaluationStatement : Prop)
#check (AKLT.Blueprint.H1.ProductBallNonnegativeStatement : Prop)
#check (AKLT.Blueprint.H1.DifferenceStructureStatement : Prop)
#check (AKLT.Blueprint.H1.ReducedStructureStatement : Prop)
#check (AKLT.Blueprint.H1.DifferenceEvaluationStatement : Prop)
#check (AKLT.Blueprint.H1.SectorSpinStableStatement : Prop)
#check (AKLT.Blueprint.H1.SectorWeightBasisStatement : Prop)
#check (AKLT.Blueprint.H1.SpanWeightLatticeStatement : Prop)
#check (AKLT.Blueprint.H1.SpinAdjointStatement : Prop)
#check (AKLT.Blueprint.H1.SpinCommutatorStatement : Prop)
#check (AKLT.Blueprint.H1.WeightLadderTransferStatement : Prop)
#check (AKLT.Blueprint.H1.CommonWeightEigenvectorStatement : Prop)
#check (AKLT.Blueprint.H1.LadderWalkStatement : Prop)
#check (AKLT.Blueprint.H1.PositiveSpectrumStatement : Prop)
#check (AKLT.Blueprint.H1.CentralWeightHalfStatement : Prop)
#check (AKLT.Blueprint.H1.PauliHermitianStatement : Prop)
#check (AKLT.Blueprint.H1.ReflectionParityStatement : Prop)
#check (AKLT.Blueprint.H1.PauliRealityStatement : Prop)
#check (AKLT.Blueprint.H1.InversionCovarianceStatement : Prop)
#check (AKLT.Blueprint.H1.AdjointPauliCoordinatesStatement : Prop)
#check (AKLT.Blueprint.H1.AdjointPauliOrthogonalStatement : Prop)
#check (AKLT.Blueprint.H1.PauliRotationTransferStatement : Prop)
#check (AKLT.Blueprint.H1.CayleyTensorCommutationStatement : Prop)
#check (AKLT.Blueprint.H1.TensorLinearCoefficientStatement : Prop)
#check (AKLT.Blueprint.H1.SpinGeneratorTransferStatement : Prop)
#check (AKLT.Blueprint.H1.MomentPauliInterchangeStatement : Prop)
#check (AKLT.Blueprint.H1.PairExpansionFromRealizationStatement : Prop)
#check (AKLT.Blueprint.H1.RetainedPairExpansionStatement : Prop)
#check (AKLT.Blueprint.H1.UnitPairSupportStatement : Prop)
#check (AKLT.Blueprint.H1.EqualPairExchangeStatement : Prop)
#check (AKLT.Blueprint.H1.PairExpansionTransferStatement : Prop)
#check (AKLT.Blueprint.H1.PairTokensDistinctStatement : Prop)

#print axioms AKLT.Blueprint.H1.momentInputs
#print axioms AKLT.Blueprint.H1.integratePassage_of_nodes
#print axioms AKLT.Blueprint.H1.leaf_of_nodes
#print axioms AKLT.Blueprint.H1.reducedStructure_of_nodes
#print axioms AKLT.Blueprint.H1.simultaneousLeafReconstruction_of_nodes
#print axioms AKLT.Blueprint.H1.reduce_of_nodes
#print axioms AKLT.Blueprint.H1.inversion_of_nodes
#print axioms AKLT.Blueprint.H1.retainedPairExpansion_of_nodes
#print axioms AKLT.Blueprint.H1.operatorStructure_of_nodes
#print axioms AKLT.Blueprint.H1.sector_of_nodes
#print axioms AKLT.Blueprint.H1.gramResidual
#print axioms AKLT.Blueprint.H1.thresholdSymmetry_of_integerCheck
#print axioms AKLT.Blueprint.H1.h1Theorem_of_certificate
#print axioms AKLT.Blueprint.H1.h1Theorem_of_parts
#print axioms AKLT.Blueprint.H1.h1_of_theorem
#print axioms AKLT.Blueprint.H1.h1_of_parts
#print axioms AKLT.Blueprint.H1.h1_of_certificateV2
#print axioms AKLT.Blueprint.H1.passageSubtraction
#print axioms AKLT.Blueprint.H1.activeStatuses
#print axioms AKLT.Blueprint.H1.singlePauliTrace
#print axioms AKLT.Blueprint.H1.inversionBall
#print axioms AKLT.Blueprint.H1.differenceEvaluation
#print axioms AKLT.Blueprint.H1.reducedStatuses
#print axioms AKLT.Blueprint.H1.centralWeightHalf
#print axioms AKLT.Blueprint.H1.pairTokensDistinct
