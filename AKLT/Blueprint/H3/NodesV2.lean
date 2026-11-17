module
public import AKLT.Blueprint.H3.NodesV2Stationary
public import AKLT.Blueprint.H3.NodesV2Quotient

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.Blueprint.H3

/-- Index package for exactly five new open V2 leaves, not an additional leaf.
Every V1 leaf remains useful and is retained byte-for-byte in its original module. -/
def AdaptationLeavesStatementV2 : Prop :=
  StationaryCoefficientOffCentreStatementV2 ∧ StationaryCentreZeroOperatorStatementV2 ∧
  StationaryContinuationBridgeStatementV2 ∧ StationaryCertificateBridgeStatementV2 ∧
  StoppedQuotientIntertwiningStatementV2

/-- Assembled clarification of `l:phase-expansion`, REF2_6 finding 2.
longOrdering is the finRange filter order: chronological straight first departures, then
chronological turns. Its identity with the actual kernel contribution is asserted only for
n>12. At shorter lengths the shared Top V2 statement concerns the separate longOrdering,
not kernelOrdering. The prefix fold retains these long-trail phase weights at length twelve.
This target is assembled from frozen algebra and Top PhaseExpansionStatementV2, not a leaf. -/
def LongTrailPhaseExpansionStatementV2 : Prop :=
  ∀ n : ℕ, ∀ X : PairType, ∀ w : DirectionWord n, ClosedTrail X w → 12 < n →
    (∑ φ : Phase, prefixPhases w φ * phaseTerminal φ) = closedContribution w ∧
    ∀ L : ℕ, ∀ hL : L ≤ n,
      let initialWord : DirectionWord L := fun i => w ⟨i.val, Nat.lt_of_lt_of_le i.isLt hL⟩
      (∑ φ : Phase, prefixPhases w φ * phaseTerminal φ) =
        ∑ φ : Phase, prefixPhases initialWord φ * truePhaseSuffix w L φ

end AKLT.Blueprint.H3
