module
public import AKLT.Blueprint.Rec.NodesV2Local

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.Blueprint.Rec

/-- `l:onepoint`: count uncovered U departures using the shared full-scope
present-bond matcher. All exception positions are counted, including late ones. -/
def uncoveredCountV2 {G : Finset Plane} {n : ℕ} (D : Network G) (u : Plane)
    (incoming : Compass) (w : DirectionWord n) : ℕ := by
  classical
  exact (Finset.univ.filter fun i : Fin n =>
    (prefixNetwork D u w i.val).status (wordVertex u w i.val) = .U ∧
    ¬ AKLT.Defs.CoveredDepartureV2 (prefixNetwork D u w i.val) (wordVertex u w i.val)
      (wordIncoming incoming w i) (w i)).card

/-- `l:onepoint`, §6 lines 711–753; ARCH_0 F1. Apply the wider shared
local comparison at covered U departures, use the uniform bound at the at most
twelve others, and take the common pointwise maximum before summing. -/
def OnePointPointwiseStatementV2 : Prop :=
  Top.H1Statement → ∀ G : Finset Plane, ∀ τ : PinAssignment G, ∀ D : Network G,
    D.Auxiliary → ∀ u : Plane, D.AdmissibleStart u → ∀ incoming : Compass,
    ¬ D.Present (u - incoming.step) u → ∀ n : ℕ, ∀ w : DirectionWord n,
    StoppedNetworkTrail D u (protectedSites G) w → uncoveredCountV2 D u incoming w ≤ 12 →
      (traceCoefficient D (wordVertices u w) : ℝ) *
        max (traceRatio D τ true (wordVertices u w)) (traceRatio D τ false (wordVertices u w)) ≤
          exceptionFactor * (trailWeight u incoming w : ℝ)

/-- `l:onepoint`, §6 lines 755–775; ARCH_0 F1. The shared matcher gives
the same sum-of-maxima bound. Preserve the absent incoming bond, original S,
positive H2 rate, and finite protected distance. -/
def OnePointSumStatementV2 : Prop :=
  Top.H1Statement → ∀ CV q : ℝ, OpenTrailBound CV q →
    ∀ G : Finset Plane, ∀ τ : PinAssignment G, ∀ D : Network G, D.Auxiliary →
    ∀ u : Plane, D.AdmissibleStart u → ∀ incoming : Compass,
    ¬ D.Present (u - incoming.step) u →
    (∀ n : ℕ, ∀ w : DirectionWord n, StoppedNetworkTrail D u (protectedSites G) w →
      uncoveredCountV2 D u incoming w ≤ 12) →
    onePointSum D τ u ≤ onePointConstant CV q * q^(protectedDistance G u)

end AKLT.Blueprint.Rec
