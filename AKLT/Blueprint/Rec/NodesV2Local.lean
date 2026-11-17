module
public import AKLT.Blueprint.Rec.Assembly
public import AKLT.Blueprint.Rec.Counterexample

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-! Adaptation to ARCH_0 F1/F1a. The shared present-bond matcher is always
fully qualified: the frozen Rec-local predicate has the same short name.
Every mathematical obligation in this file is an open, closed Prop. -/

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.Blueprint.Rec

/-- `l:local`, §6 lines 555–646; ARCH_0 F1/F1a. Match only internal
present bonds and non-tip statuses. Tip cover bonds may be added, never lost.
Resolve the effective tips and both corner slots into a common nonnegative
mixture, without matching any external kept direction. -/
def LocalMixtureStatementV2 : Prop :=
  ∀ a : Departure, a.D.status a.y = .U → ∀ incoming outgoing : Compass,
    a.o = a.y + outgoing.step → AKLT.Defs.CoveredDepartureV2 a.D a.y incoming outgoing →
    ∃ k : ℕ, ∃ π : Fin k → PatternData, ∃ m : Fin k → (Fin 20 → UnitVector),
      ∃ weight : Fin k → ℝ,
      (∀ i, 0 ≤ weight i ∧ (π i).Covered ∧
        ((π i).outgoing = .north ↔ outgoing = incoming)) ∧
      a.D.partition a.τ true (fun _ => 1) = ∑ i, weight i * patternCurrent (π i) (m i) ∧
      (traceStep a.D a.y a.o).partition a.τ true (fun _ => 1) =
        ∑ i, weight i * patternNext (π i) (m i)

/-- `l:local`, §6 lines 625–651; ARCH_0 F1. Apply H1 to the shared
matcher, allowing arbitrary missing external factors and inactive flags.
The actual outgoing neighbor is supplied by Departure, not inferred from a slot. -/
def CoveredRatioStatementV2 : Prop :=
  Top.H1Statement → ∀ a : Departure, a.D.status a.y = .U →
    ∀ incoming outgoing : Compass, a.o = a.y + outgoing.step →
      AKLT.Defs.CoveredDepartureV2 a.D a.y incoming outgoing →
      stepRatio a.D a.τ true a.y a.o ≤ (passageFactor (decide (outgoing = incoming)) : ℝ)

/-- `l:response-typed`, §7 lines 419–429, 462–506; ARCH_0 F1/F1a.
Use the shared internal-present-bond cover and positive integrated J to pass
from H1 to I^tau >= c J^tau, or I2^tau >= c. The numeric conclusions are unchanged. -/
def CoveredIntegratedLowerStatementV2 : Prop :=
  Top.H1Statement → ∀ a : Departure, a.D.status a.y = .U →
    ∀ incoming outgoing : Compass, a.o = a.y + outgoing.step →
      AKLT.Defs.CoveredDepartureV2 a.D a.y incoming outgoing →
      let c : ℝ := localThreshold (decide (outgoing = incoming))
      (∀ f : Plane, a.D.presentNeighbors a.y = {a.o, f} → a.o ≠ f →
        c ≤ responseI₂ a.D a.τ true a.y a.o f) ∧
      ∀ f g : Plane, a.D.presentNeighbors a.y = {a.o, f, g} →
        a.o ≠ f → a.o ≠ g → f ≠ g →
        c * responseJ a.D a.τ true a.y f g ≤ responseI a.D a.τ true a.y a.o f g

/-- `d:pattern`, §6 lines 488–519; ARCH_0 F1a. The frozen intersection
matcher is a sufficient specialization of shared internal-bond matching.
Only this implication is proposed; external flags prevent a converse. -/
def LegacyCoverComparisonStatementV2 : Prop :=
  ∀ G : Finset Plane, ∀ D : Network G, D.Auxiliary → ∀ y : Plane,
    ∀ incoming outgoing : Compass,
      AKLT.Blueprint.Rec.CoveredDepartureV2 D y incoming outgoing →
        AKLT.Defs.CoveredDepartureV2 D y incoming outgoing

/-- `l:local`, §6 lines 568–640; ARCH_0 F1/F1a. Migrate the retained
boundary-corner diagnostic to the shared matcher. This is a new open task;
the old kernel computation proves only the frozen local matcher claim. -/
def BoundaryExampleCoveredStatementV2 : Prop :=
  AKLT.Defs.CoveredDepartureV2 (normalizeStart boundaryExampleD (0, 0) (-1, 0))
    (0, 0) .east .east

end AKLT.Blueprint.Rec
