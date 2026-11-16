import AKLT.Blueprint.Win.LibraryChecks

/-! Closedness and kernel-dependency audit for every delivered node and assembly. -/

#check (AKLT.Blueprint.Win.ShellScaleStatement : Prop)
#check (AKLT.Blueprint.Win.CloseCornerStatement : Prop)
#check (AKLT.Blueprint.Win.ExceptionalLocalizationStatement : Prop)
#check (AKLT.Blueprint.Win.RadiusGapStatement : Prop)
#check (AKLT.Blueprint.Win.ExceptionalCountStatement : Prop)
#check (AKLT.Blueprint.Win.SideCornerWitnessStatement : Prop)
#check (AKLT.Blueprint.Win.NearShellCountStatement : Prop)
#check (AKLT.Blueprint.Win.ShellInclusionStatement : Prop)
#check (AKLT.Blueprint.Win.PredecessorShellStatement : Prop)
#check (AKLT.Blueprint.Win.SeedSeparationStatement : Prop)
#check (AKLT.Blueprint.Win.MetricFactsStatement : Prop)
#check (AKLT.Blueprint.Win.FiniteDepthStatement : Prop)
#check (AKLT.Blueprint.Win.BoundaryMembershipStatement : Prop)
#check (AKLT.Blueprint.Win.ChainBoxStatement : Prop)
#check (AKLT.Blueprint.Win.DiagonalEliminationStatement : Prop)
#check (AKLT.Blueprint.Win.ColumnFluxStatement : Prop)
#check (AKLT.Blueprint.Win.TailSupportStatement : Prop)
#check (AKLT.Blueprint.Win.PlaquetteReconstructionStatement : Prop)
#check (AKLT.Blueprint.Win.PlaquetteTrianglesStatement : Prop)
#check (AKLT.Blueprint.Win.CutEdgesNonemptyStatement : Prop)
#check (AKLT.Blueprint.Win.LinkedSeparationStatement : Prop)
#check (AKLT.Blueprint.Win.TriangleCutParityStatement : Prop)
#check (AKLT.Blueprint.Win.SpanCutParityStatement : Prop)
#check (AKLT.Blueprint.Win.TwoCrossingCycleStatement : Prop)
#check (AKLT.Blueprint.Win.TwoCrossingParityStatement : Prop)
#check (AKLT.Blueprint.Win.OuterEndpointTransferStatement : Prop)
#check (AKLT.Blueprint.Win.CrossFactsStatement : Prop)
#check (AKLT.Blueprint.Win.CrossOverlapStatement : Prop)
#check (AKLT.Blueprint.Win.CrossUnionStatement : Prop)
#check (AKLT.Blueprint.Win.NeighbourDecayStatement : Prop)
#check (AKLT.Blueprint.Win.CrossWeightSumStatement : Prop)
#check (AKLT.Blueprint.Win.ConnectedEnumerationStatement : Prop)
#check (AKLT.Blueprint.Win.CutScalesStatement : Prop)
#check (AKLT.Blueprint.Win.CoreConnectedStatement : Prop)
#check (AKLT.Blueprint.Win.RadialPathsStatement : Prop)
#check (AKLT.Blueprint.Win.SquareExteriorStatement : Prop)
#check (AKLT.Blueprint.Win.ComplementEscapeStatement : Prop)
#check (AKLT.Blueprint.Win.WindowBufferStatement : Prop)
#check (AKLT.Blueprint.Win.RawRangeStatement : Prop)
#check (AKLT.Blueprint.Win.RawDistanceObstructionsStatement : Prop)
#check (AKLT.Blueprint.Win.RawDepthArithmeticStatement : Prop)
#check (AKLT.Blueprint.Win.RawHeightStatement : Prop)
#check (AKLT.Blueprint.Win.SignedSideExclusionStatement : Prop)
#check (AKLT.Blueprint.Win.SquareIntersectionStatement : Prop)
#check (AKLT.Blueprint.Win.RawLayerCountStatement : Prop)
#check (AKLT.Blueprint.Win.NearSeriesStatement : Prop)
#check (AKLT.Blueprint.Win.RawWeightSumStatement : Prop)
#check (AKLT.Blueprint.Win.ThickDepthStatement : Prop)
#check (AKLT.Blueprint.Win.CutSeparationStatement : Prop)
#check (AKLT.Blueprint.Win.OriginalPositivityStatement : Prop)
#check (AKLT.Blueprint.Win.PartLawBridgeStatement : Prop)
#check (AKLT.Blueprint.Win.EnumerationStepsStatement : Prop)
#check (AKLT.Blueprint.Win.SurvivorGeometryStatement : Prop)
#check (AKLT.Blueprint.Win.RemovalIntegralStatement : Prop)
#check (AKLT.Blueprint.Win.NeighbourFibresStatement : Prop)
#check (AKLT.Blueprint.Win.PairMeanAveragingStatement : Prop)
#check (AKLT.Blueprint.Win.QuarticMeanBoundStatement : Prop)
#check (AKLT.Blueprint.Win.PolynomialLowerStatement : Prop)
#check (AKLT.Blueprint.Win.RemovedPairResponseStatement : Prop)
#check (AKLT.Blueprint.Win.PairDifferenceStatement : Prop)
#check (AKLT.Blueprint.Win.LogLipschitzStatement : Prop)
#check (AKLT.Blueprint.Win.LogStepIdentityStatement : Prop)
#check (AKLT.Blueprint.Win.LocalLogEstimateStatement : Prop)
#check (AKLT.Blueprint.Win.RemovalTelescopeStatement : Prop)
#check (AKLT.Blueprint.Win.RemovalCostSumStatement : Prop)
#check (AKLT.Blueprint.Win.FrameFibreSumStatement : Prop)
#check (AKLT.Blueprint.Win.ComplementQuadratureStatement : Prop)
#check (AKLT.Blueprint.Win.MarginalNormalizationStatement : Prop)
#check (AKLT.Blueprint.Win.OriginalFactorizationStatement : Prop)
#check (AKLT.Blueprint.Win.ComponentPinsStatement : Prop)
#check (AKLT.Blueprint.Win.WindowWeightPositiveStatement : Prop)
#check (AKLT.Blueprint.Win.WindowRewriteStatement : Prop)
#check (AKLT.Blueprint.Win.BoundedTiltStatement : Prop)
#check (AKLT.Blueprint.Win.OverlapMinorizationStatement : Prop)
#check (AKLT.Blueprint.Win.TailExponentialStatement : Prop)
#check (AKLT.Blueprint.Win.TailThresholdStatement : Prop)
#check (AKLT.Blueprint.Win.CutCostNonnegativeStatement : Prop)
#check (AKLT.Blueprint.Win.WindowCostArithmeticStatement : Prop)
#check (AKLT.Blueprint.Win.FrameWeightPositiveStatement : Prop)

#check (AKLT.Blueprint.Top.ShellGeometryStatement : Prop)
#check (AKLT.Blueprint.Top.CutMOSStatement : Prop)

#print axioms AKLT.Blueprint.Win.shellGeometry_of_leaves
#print axioms AKLT.Blueprint.Win.evenChain_of_leaves
#print axioms AKLT.Blueprint.Win.boundaryConnectivity_of_leaves
#print axioms AKLT.Blueprint.Win.thickening_of_leaves
#print axioms AKLT.Blueprint.Win.taperConnectivity_of_leaves
#print axioms AKLT.Blueprint.Win.cutGeometry_of_leaves
#print axioms AKLT.Blueprint.Win.removalEstimate_of_leaves
#print axioms AKLT.Blueprint.Win.cutMinorization_of_leaves
#print axioms AKLT.Blueprint.Win.cutMOS_of_leaves
#print axioms AKLT.Blueprint.Win.metricFacts
#print axioms AKLT.Blueprint.Win.spanCutParity
#print axioms AKLT.Blueprint.Win.logLipschitz
#print axioms AKLT.Blueprint.Win.cutCostNonnegative
#print axioms AKLT.Blueprint.Win.windowCostArithmetic
