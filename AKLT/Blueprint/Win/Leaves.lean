import AKLT.Blueprint.Win.NodesShell
import AKLT.Blueprint.Win.NodesTopology
import AKLT.Blueprint.Win.NodesTaper
import AKLT.Blueprint.Win.NodesRemoval
import AKLT.Blueprint.Win.NodesCut
import AKLT.Blueprint.Win.NodesTail

namespace AKLT.Blueprint.Win

structure ShellLeaves : Prop where
  shellScale : ShellScaleStatement
  closeCorner : CloseCornerStatement
  exceptionalLocalization : ExceptionalLocalizationStatement
  radiusGap : RadiusGapStatement
  exceptionalCount : ExceptionalCountStatement
  sideCornerWitness : SideCornerWitnessStatement
  nearShellCount : NearShellCountStatement
  shellInclusion : ShellInclusionStatement
  predecessorShell : PredecessorShellStatement
  seedSeparation : SeedSeparationStatement

structure TopologyLeaves : Prop where
  finiteDepth : FiniteDepthStatement
  boundaryMembership : BoundaryMembershipStatement
  chainBox : ChainBoxStatement
  diagonalElimination : DiagonalEliminationStatement
  columnFlux : ColumnFluxStatement
  tailSupport : TailSupportStatement
  plaquetteReconstruction : PlaquetteReconstructionStatement
  plaquetteTriangles : PlaquetteTrianglesStatement
  cutEdgesNonempty : CutEdgesNonemptyStatement
  linkedSeparation : LinkedSeparationStatement
  triangleCutParity : TriangleCutParityStatement
  twoCrossingCycle : TwoCrossingCycleStatement
  twoCrossingParity : TwoCrossingParityStatement
  outerEndpointTransfer : OuterEndpointTransferStatement
  crossFacts : CrossFactsStatement
  crossOverlap : CrossOverlapStatement
  crossUnion : CrossUnionStatement
  neighbourDecay : NeighbourDecayStatement
  crossWeightSum : CrossWeightSumStatement
  connectedEnumeration : ConnectedEnumerationStatement

structure TaperLeaves : Prop where
  cutScales : CutScalesStatement
  coreConnected : CoreConnectedStatement
  radialPaths : RadialPathsStatement
  squareExterior : SquareExteriorStatement
  complementEscape : ComplementEscapeStatement
  windowBuffer : WindowBufferStatement
  rawRange : RawRangeStatement
  rawDistanceObstructions : RawDistanceObstructionsStatement
  rawDepthArithmetic : RawDepthArithmeticStatement
  rawHeight : RawHeightStatement
  signedSideExclusion : SignedSideExclusionStatement
  squareIntersection : SquareIntersectionStatement
  rawLayerCount : RawLayerCountStatement
  nearSeries : NearSeriesStatement
  rawWeightSum : RawWeightSumStatement
  thickDepth : ThickDepthStatement
  cutSeparation : CutSeparationStatement

structure RemovalLeaves : Prop where
  originalPositivity : OriginalPositivityStatement
  partLawBridge : PartLawBridgeStatement
  enumerationSteps : EnumerationStepsStatement
  survivorGeometry : SurvivorGeometryStatement
  removalIntegral : RemovalIntegralStatement
  neighbourFibres : NeighbourFibresStatement
  pairMeanAveraging : PairMeanAveragingStatement
  quarticMeanBound : QuarticMeanBoundStatement
  polynomialLower : PolynomialLowerStatement
  removedPairResponse : RemovedPairResponseStatement
  pairDifference : PairDifferenceStatement
  logStepIdentity : LogStepIdentityStatement
  localLogEstimate : LocalLogEstimateStatement
  removalTelescope : RemovalTelescopeStatement
  removalCostSum : RemovalCostSumStatement

structure CutLeaves : Prop where
  frameFibreSum : FrameFibreSumStatement
  complementQuadrature : ComplementQuadratureStatement
  marginalNormalization : MarginalNormalizationStatement
  originalFactorization : OriginalFactorizationStatement
  componentPins : ComponentPinsStatement
  windowWeightPositive : WindowWeightPositiveStatement
  windowRewrite : WindowRewriteStatement
  boundedTilt : BoundedTiltStatement
  overlapMinorization : OverlapMinorizationStatement
  frameWeightPositive : FrameWeightPositiveStatement

structure TailLeaves : Prop where
  tailExponential : TailExponentialStatement
  tailThreshold : TailThresholdStatement

/-- A closed conjunction of the open blueprint obligations. -/
structure WindowLeaves : Prop where
  shell : ShellLeaves
  topology : TopologyLeaves
  taper : TaperLeaves
  removal : RemovalLeaves
  cut : CutLeaves
  tail : TailLeaves

end AKLT.Blueprint.Win
