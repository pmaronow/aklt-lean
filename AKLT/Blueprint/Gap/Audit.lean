import AKLT.Blueprint.Gap.All

-- Every statement is a closed Prop, with all instances quantified inside it.
#check (AKLT.Blueprint.Gap.FibreNormalizationStatement : Prop)
#check (AKLT.Blueprint.Gap.ConditionalProjectionStatement : Prop)
#check (AKLT.Blueprint.Gap.ConditionalVarianceStatement : Prop)
#check (AKLT.Blueprint.Gap.MaximalCouplingStatement : Prop)
#check (AKLT.Blueprint.Gap.CouplingMarginalTVStatement : Prop)
#check (AKLT.Blueprint.Gap.MarginalCompletionStatement : Prop)
#check (AKLT.Blueprint.Gap.HammingLocalizationStatement : Prop)
#check (AKLT.Blueprint.Gap.CommonMinorizationStatement : Prop)
#check (AKLT.Blueprint.Gap.SurgeryPreservationStatement : Prop)
#check (AKLT.Blueprint.Gap.ConditionalPatchCouplingStatement : Prop)
#check (AKLT.Blueprint.Gap.FrameProductReferenceStatement : Prop)
#check (AKLT.Blueprint.Gap.FrameInteractionBoundsStatement : Prop)
#check (AKLT.Blueprint.Gap.NormalizedInteractionStatement : Prop)
#check (AKLT.Blueprint.Gap.SignedFrameBlockStatement : Prop)
#check (AKLT.Blueprint.Gap.VariationalCenteringStatement : Prop)
#check (AKLT.Blueprint.Gap.ProductTensorizationStatement : Prop)
#check (AKLT.Blueprint.Gap.DensityComparisonStatement : Prop)
#check (AKLT.Blueprint.Gap.ConditionalBlockComparisonStatement : Prop)
#check (AKLT.Blueprint.Gap.MultiplicityEstimateStatement : Prop)
#check (AKLT.Blueprint.Gap.HammingPathStatement : Prop)
#check (AKLT.Blueprint.Gap.LipschitzCouplingStatement : Prop)
#check (AKLT.Blueprint.Gap.LipschitzEigenvalueStatement : Prop)
#check (AKLT.Blueprint.Gap.ReversibleEigenvalueGapStatement : Prop)
#check (AKLT.Blueprint.Gap.ReversibleSpectralStatement : Prop)
#check (AKLT.Blueprint.Gap.BlockAverageFormStatement : Prop)
#check (AKLT.Blueprint.Gap.ProductPoincareTransportStatement : Prop)
#check (AKLT.Blueprint.Gap.ProductCouplingTransportStatement : Prop)
#check (AKLT.Blueprint.Gap.ThresholdSpacingStatement : Prop)
#check (AKLT.Blueprint.Gap.GroundOrthogonalityStatement : Prop)
#check (AKLT.Blueprint.Gap.RayleighBoundStatement : Prop)
#check (AKLT.Blueprint.Gap.StoppedCouplingStatement : Prop)
#check (AKLT.Blueprint.Gap.HammingAtScaleStatement : Prop)
#check (AKLT.Blueprint.Gap.FiniteContractionStatement : Prop)
#check (AKLT.Blueprint.Gap.BlockComparisonStatement : Prop)
#check (AKLT.Blueprint.Gap.PeriodicCriterionStatement : Prop)
#check (AKLT.Blueprint.Gap.PositiveToProbabilityStatement : Prop)
#check (AKLT.Blueprint.Gap.IndependentPairsStatement : Prop)
#check (AKLT.Blueprint.Gap.DiagonalCouplingStatement : Prop)
#check (AKLT.Blueprint.Gap.DeltaBoundsStatement : Prop)
#check (AKLT.Blueprint.Gap.PowerCountStatement : Prop)
#check (AKLT.Blueprint.Gap.PoincareMonotoneStatement : Prop)
#check (AKLT.Blueprint.Gap.ContainingBlockCountStatement : Prop)
#check (AKLT.Blueprint.Gap.ExteriorBlockCountStatement : Prop)
#check (AKLT.Blueprint.Gap.BlockVolumeBoundStatement : Prop)
#check (AKLT.Blueprint.Gap.PeriodicNeighbourCouplingStatement : Prop)
#check (AKLT.Blueprint.Gap.PeriodicBudgetStatement : Prop)
#check (AKLT.Blueprint.Gap.TorusColourStatement : Prop)
#check (AKLT.Blueprint.Gap.PullbackColourStatement : Prop)
#check (AKLT.Blueprint.Gap.HaloInjectionStatement : Prop)
#check (AKLT.Blueprint.Gap.LiftBondStatement : Prop)
#check (AKLT.Blueprint.Gap.BoxCoordinatesStatement : Prop)
#check (AKLT.Blueprint.Gap.BoxGaugeLawStatement : Prop)
#check (AKLT.Blueprint.Gap.TorusRangeTransferStatement : Prop)
#check (AKLT.Blueprint.Gap.SquareInternalEdgesStatement : Prop)
#check (AKLT.Blueprint.Gap.FrameSpecRegularityStatement : Prop)
#check (AKLT.Blueprint.Gap.FrameSpecEnergyStatement : Prop)
#check (AKLT.Blueprint.Gap.FrameWindowTransferStatement : Prop)
#check (AKLT.Blueprint.Gap.ShellNestingStatement : Prop)
#check (AKLT.Blueprint.Gap.FiniteEnergyChainStatement : Prop)
#check (AKLT.Blueprint.Gap.ShellRowStatement : Prop)
#check (AKLT.Blueprint.Gap.TraceMarginalsStatement : Prop)
#check (AKLT.Blueprint.Gap.TrialCountStatement : Prop)
#check (AKLT.Blueprint.Gap.ShellAbsorptionStatement : Prop)
#check (AKLT.Blueprint.Gap.FiniteTrialFailureStatement : Prop)
#check (AKLT.Blueprint.Gap.TraceDisagreementStatement : Prop)
#check (AKLT.Blueprint.Gap.TerminalRadiusStatement : Prop)
#check (AKLT.Blueprint.Gap.ScaleExistenceStatement : Prop)
#check (AKLT.Blueprint.Gap.BinomialTailStatement : Prop)
#check (AKLT.Blueprint.Gap.ScaleGeometryStatement : Prop)
#check (AKLT.Blueprint.Gap.HammingCardinalityStatement : Prop)
#check (AKLT.Blueprint.Gap.HammingBudgetStatement : Prop)
#check (AKLT.Blueprint.Gap.FarBoundaryEqualityStatement : Prop)
#check (AKLT.Blueprint.Gap.StoppedHammingConversionStatement : Prop)

#check (AKLT.Blueprint.Gap.mainW_of_parts :
  AKLT.Blueprint.Gap.FiniteAssemblyLeaves → AKLT.Blueprint.Gap.ShellAssemblyLeaves →
  AKLT.Blueprint.Gap.PeriodicAssemblyLeaves → AKLT.Blueprint.Top.ShellGeometryStatement →
  AKLT.Blueprint.Top.ThreeFramesStatement → AKLT.Blueprint.Top.StarStatement →
  AKLT.Blueprint.Top.PlaneEnergyStatement → AKLT.Blueprint.Top.QDStatement →
  AKLT.Blueprint.Top.TorusKernelStatement → AKLT.Blueprint.Top.MainWStatement)

#print axioms AKLT.Blueprint.Gap.reversibleSpectral_of_parts
#print axioms AKLT.Blueprint.Gap.finiteContraction_of_parts
#print axioms AKLT.Blueprint.Gap.blockComparison_of_parts
#print axioms AKLT.Blueprint.Gap.periodicCriterion_of_parts
#print axioms AKLT.Blueprint.Gap.stoppedCoupling_of_parts
#print axioms AKLT.Blueprint.Gap.hammingAtScale_of_parts
#print axioms AKLT.Blueprint.Gap.mainW_of_core
#print axioms AKLT.Blueprint.Gap.mainW_of_parts
#print axioms AKLT.Blueprint.Gap.groundOrthogonality
#print axioms AKLT.Blueprint.Gap.rayleighBound
#print axioms AKLT.Blueprint.Gap.positiveToProbability
#print axioms AKLT.Blueprint.Gap.independentPairsProbability
#print axioms AKLT.Blueprint.Gap.diagonalCoupling
#print axioms AKLT.Blueprint.Gap.deltaBounds
#print axioms AKLT.Blueprint.Gap.powerCount
#print axioms AKLT.Blueprint.Gap.poincareMonotone
#print axioms AKLT.Blueprint.Gap.periodicBudget
