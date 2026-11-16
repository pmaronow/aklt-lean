import AKLT.Blueprint.Q.Assembly

/-! Closedness and axiom audit; no open leaf is asserted. -/

#check (AKLT.Blueprint.Q.FrameWeightsPositiveStatement : Prop)
#check (AKLT.Blueprint.Q.PositiveNormalizationStatement : Prop)
#check (AKLT.Blueprint.Q.PlaneConditioningStatement : Prop)
#check (AKLT.Blueprint.Q.TorusMarkovStatement : Prop)
#check (AKLT.Blueprint.Q.PlaneOneSiteEnergyStatement : Prop)
#check (AKLT.Blueprint.Q.TorusOneSiteEnergyStatement : Prop)
#check (AKLT.Blueprint.Q.PartialAssignmentStatement : Prop)
#check (AKLT.Blueprint.Q.PlaneAssignmentReindexStatement : Prop)
#check (AKLT.Blueprint.Q.PlaneProductReferenceStatement : Prop)
#check (AKLT.Blueprint.Q.BoundaryAbsorptionStatement : Prop)
#check (AKLT.Blueprint.Q.PlaneDensityBoundsStatement : Prop)
#check (AKLT.Blueprint.Q.DensityVarianceStatement : Prop)
#check (AKLT.Blueprint.Q.DensityDirichletStatement : Prop)
#check (AKLT.Blueprint.Q.ProductPoincareStatement : Prop)
#check (AKLT.Blueprint.Q.RotationStatement : Prop)
#check (AKLT.Blueprint.Q.RotationPowersStatement : Prop)
#check (AKLT.Blueprint.Q.FrameScalarsStatement : Prop)
#check (AKLT.Blueprint.Q.OrthogonalFamilyStatement : Prop)
#check (AKLT.Blueprint.Q.OneSiteMomentEncodingStatement : Prop)
#check (AKLT.Blueprint.Q.IcoDistanceStatement : Prop)
#check (AKLT.Blueprint.Q.RotationDisplacementStatement : Prop)
#check (AKLT.Blueprint.Q.SelfRotationStatement : Prop)
#check (AKLT.Blueprint.Q.DisplacedDistanceStatement : Prop)
#check (AKLT.Blueprint.Q.RelativeRotationStatement : Prop)
#check (AKLT.Blueprint.Q.StateEvaluationStatement : Prop)
#check (AKLT.Blueprint.Q.VbsHomogeneityStatement : Prop)
#check (AKLT.Blueprint.Q.CoefficientReconstructionStatement : Prop)
#check (AKLT.Blueprint.Q.PairSpinFourStatement : Prop)
#check (AKLT.Blueprint.Q.PairDiagonalDivisionStatement : Prop)
#check (AKLT.Blueprint.Q.SpectatorDivisibilityStatement : Prop)
#check (AKLT.Blueprint.Q.SingletPrimeStatement : Prop)
#check (AKLT.Blueprint.Q.SingletNonassociateStatement : Prop)
#check (AKLT.Blueprint.Q.PrimeProductStatement : Prop)
#check (AKLT.Blueprint.Q.IncidentKernelStatement : Prop)
#check (AKLT.Blueprint.Q.IncidentDegreeStatement : Prop)
#check (AKLT.Blueprint.Q.DeterminantModulusStatement : Prop)
#check (AKLT.Blueprint.Q.GroundProductWeightStatement : Prop)
#check (AKLT.Blueprint.Q.IncidentEvaluationStatement : Prop)
#check (AKLT.Blueprint.Q.GroundFibreFactorizationStatement : Prop)
#check (AKLT.Blueprint.Q.GroundTransformStatement : Prop)
#check (AKLT.Blueprint.Q.FibreIntertwiningStatement : Prop)
#check (AKLT.Blueprint.Q.FibreProjectionStatement : Prop)
#check (AKLT.Blueprint.Q.WeightedPolarizationStatement : Prop)
#check (AKLT.Blueprint.Q.GroundQuotientVarianceStatement : Prop)
#check (AKLT.Blueprint.Q.BetaNonzeroStatement : Prop)
#check (AKLT.Blueprint.Q.PairDiagonalRankStatement : Prop)
#check (AKLT.Blueprint.Q.PairTopInclusionStatement : Prop)
#check (AKLT.Blueprint.Q.PairTopDimensionStatement : Prop)
#check (AKLT.Blueprint.Q.FourVariableDeterminantPrimeStatement : Prop)
#check (AKLT.Blueprint.Q.DeterminantPrimeEmbeddingStatement : Prop)
#check (AKLT.Blueprint.Q.CentreDegreeCancellationStatement : Prop)
#check (AKLT.Blueprint.Q.IncidentProductDegreeStatement : Prop)
#check (AKLT.Blueprint.Q.StateCentreDegreeStatement : Prop)
#check (AKLT.Blueprint.Q.StarEdgeEnumerationStatement : Prop)
#check (AKLT.Blueprint.Q.StarCasimirChartStatement : Prop)
#check (AKLT.Blueprint.Q.StarProjectorTransportStatement : Prop)
#check (AKLT.Blueprint.Q.StarPositiveStatement : Prop)
#check (AKLT.Blueprint.Q.StarWitnessStatement : Prop)
#check (AKLT.Blueprint.Q.PositiveSpectralMinimumStatement : Prop)
#check (AKLT.Blueprint.Q.SpectralKernelCoercivityStatement : Prop)
#check (AKLT.Blueprint.Q.StarRelabellingStatement : Prop)
#check (AKLT.Blueprint.Q.StarAmplificationStatement : Prop)
#check (AKLT.Blueprint.Q.IncidentDoubleCountStatement : Prop)
#check (AKLT.Blueprint.Q.SpinorChoiceStatement : Prop)
#check (AKLT.Blueprint.Q.QuarticKernelDegreeStatement : Prop)
#check (AKLT.Blueprint.Q.QuarticKernelEvaluationStatement : Prop)
#check (AKLT.Blueprint.Q.ComplexQuadratureStatement : Prop)
#check (AKLT.Blueprint.Q.QuarticOffDiagonalStatement : Prop)
#check (AKLT.Blueprint.Q.QuarticDiagonalStatement : Prop)
#check (AKLT.Blueprint.Q.ResolutionExpansionStatement : Prop)
#check (AKLT.Blueprint.Q.TensorResolutionStatement : Prop)

#print axioms AKLT.Blueprint.Q.threeFrames_of_leaves
#print axioms AKLT.Blueprint.Q.resolution_of_leaves
#print axioms AKLT.Blueprint.Q.tight_of_leaves
#print axioms AKLT.Blueprint.Q.star_of_leaves
#print axioms AKLT.Blueprint.Q.density_poincare_of_leaves
#print axioms AKLT.Blueprint.Q.planeEnergy_of_leaves
#print axioms AKLT.Blueprint.Q.localKernelFactorization_of_leaves
#print axioms AKLT.Blueprint.Q.groundEvaluation_of_leaves
#print axioms AKLT.Blueprint.Q.normalize_from_scaled
#print axioms AKLT.Blueprint.Q.qd_of_leaves
#print axioms AKLT.Blueprint.Q.pairSpinFour_of_leaves
#print axioms AKLT.Blueprint.Q.singletPrime_of_leaves
#print axioms AKLT.Blueprint.Q.incidentDegree_of_leaves
#print axioms AKLT.Blueprint.Q.starRelabelling_of_leaves
#print axioms AKLT.Blueprint.Q.allTargets_of_leaves
#print axioms AKLT.Blueprint.Q.positiveNormalization
#print axioms AKLT.Blueprint.Q.rotation
#print axioms AKLT.Blueprint.Q.rotationPowers
#print axioms AKLT.Blueprint.Q.frameScalars
#print axioms AKLT.Blueprint.Q.primeProduct
#print axioms AKLT.Blueprint.Q.incidentDoubleCount
