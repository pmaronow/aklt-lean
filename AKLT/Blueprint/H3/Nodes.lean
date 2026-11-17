module
public import AKLT.Blueprint.H3.NodesAutomaton
public import AKLT.Blueprint.H3.NodesPhase
public import AKLT.Blueprint.H3.NodesDomination
public import AKLT.Blueprint.H3.NodesCertificate
public import AKLT.Blueprint.H3.NodesPrefix
public import AKLT.Blueprint.H3.NodesReflection
public import AKLT.Blueprint.H3.NodesKernel

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.Blueprint.H3

/-- Index package for the thirty open leaves, not an additional leaf. Every constituent
is a closed proposition and no constituent's type mentions another leaf Statement. -/
def AnalyticLeavesStatement : Prop :=
  RawSuccessorStatement ∧ ProjectionRealizationStatement ∧
  PhaseFoldExpansionStatement ∧ SingleChangeFactorStatement ∧
  ExposureListExpansionStatement ∧ LongOrderingMultiplierStatement ∧
  PrefixCoefficientCausalityStatement ∧ PhaseSplitAlgebraStatement ∧
  SuffixWindowValidityStatement ∧ SuffixWindowLabelsStatement ∧
  IncidentBondBudgetStatement ∧ DepartureBalanceStatement ∧ KnownSiteMemoryStatement ∧
  TrueRewardIdentityStatement ∧ RewardForgettingStatement ∧ LocalCoefficientComparisonStatement ∧
  ClosedTrailStepGeometryStatement ∧ SuffixWordComparisonStatement ∧ StationaryWordExpansionStatement ∧
  StationaryFreeEdgeStatement ∧ LongTrailPrefixStatement ∧ LongRowRegroupingStatement ∧
  ReflectionGeometryStatement ∧ ReflectionLivePairsStatement ∧ ReflectionPairLabelsStatement ∧
  FirstDirectionPartitionStatement ∧ LengthShiftSupportStatement ∧ LengthRewardPartitionStatement ∧
  KernelSeriesRegroupingStatement ∧ CutoffSeriesLiftStatement

end AKLT.Blueprint.H3
