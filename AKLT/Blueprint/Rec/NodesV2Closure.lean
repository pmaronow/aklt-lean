module
public import AKLT.Blueprint.Rec.NodesV2Walk

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.Blueprint.Rec

/-- `l:closure`: the distinct active neighbors other than the arrival site.
Presence is derived by consistency at a live U site, not presumed for an arrival. -/
def nonarrivalNeighborsV2 {G : Finset Plane} (D : Network G) (y : Plane)
    (incoming : Compass) : Finset Plane :=
  (neighbors y).erase (y - incoming.step) ∩ D.active

/-- `l:closure`, §7 lines 147–158; ARCH_0 F1/F1a. Check shared internal
present bonds, non-tip statuses and the one-sided tip condition. External
directions and flags to removed sites impose no matching requirements. -/
def CoveredClosureStatementV2 : Prop :=
  ∀ p : PairSetup, ∀ T : Finset Plane, ∀ n : ℕ, ∀ w : DirectionWord n,
    StoppedNetworkTrail p.normalized p.u T w → ∀ i : Fin n,
    (prefixNetwork p.normalized p.u w i.val).status (wordVertex p.u w i.val) = .U →
      AKLT.Defs.CoveredDepartureV2 (prefixNetwork p.normalized p.u w i.val)
        (wordVertex p.u w i.val) (wordIncoming p.incoming w i) (w i)

/-- `l:closure`, §7 lines 79–81, 158–164; REF2_5 finding 1. Only
non-arrival neighbors are response endpoints. An arrival D site can retain
two present bonds after live-site deletion and is deliberately excluded. -/
def PairClosureStatementV2 : Prop :=
  ∀ p : PairSetup, ∀ T : Finset Plane, ∀ n : ℕ, ∀ w : DirectionWord n,
    StoppedNetworkTrail p.normalized p.u T w → ∀ i : Fin n,
    let E := prefixNetwork p.normalized p.u w i.val
    let y := wordVertex p.u w i.val
    let incoming := wordIncoming p.incoming w i
    E.status y = .U →
    ∀ a ∈ nonarrivalNeighborsV2 E y incoming,
    ∀ b ∈ nonarrivalNeighborsV2 E y incoming, a ≠ b →
      (removeSite E y).ResponsePair (responsePairType {a, b}) a b y

/-- `l:terminalcover`, §7 lines 212–240; ARCH_0 F1. Repeat the one-fixed-
defect invariant with the shared matcher. Before hitting original S, every
uncovered U site is within the punctured radius-two diamond of the first hit. -/
def TerminalExceptionLocationStatementV2 : Prop :=
  ∀ p : PairSetup, p.v ∉ protectedSites p.G → ∀ n : ℕ, ∀ w : DirectionWord n,
    StoppedNetworkTrail p.normalized p.u (insert p.v (protectedSites p.G)) w →
    wordVertex p.u w n ∈ protectedSites p.G →
    let E := normalizeStart (traceNetwork p.normalized (wordVertices p.u w)) p.v p.c
    ∀ incoming : Compass, p.v = p.c + incoming.step → ∀ m : ℕ, ∀ w' : DirectionWord m,
      StoppedNetworkTrail E p.v (protectedSites p.G) w' → ∀ i : Fin m,
      (prefixNetwork E p.v w' i.val).status (wordVertex p.v w' i.val) = .U →
      ¬ AKLT.Defs.CoveredDepartureV2 (prefixNetwork E p.v w' i.val)
        (wordVertex p.v w' i.val) (wordIncoming incoming w' i) (w' i) →
      0 < latticeDist (wordVertex p.v w' i.val) (wordVertex p.u w n) ∧
        latticeDist (wordVertex p.v w' i.val) (wordVertex p.u w n) ≤ 2

/-- `l:terminalcover`, §7 lines 233–244; ARCH_0 F1. Count the shared-
matcher exceptions by injectivity of U departures into twelve sites. Both
starts remain interior, original legs remain, and exceptions may occur anywhere. -/
def TerminalExceptionCountStatementV2 : Prop :=
  ∀ p : PairSetup, p.v ∉ protectedSites p.G → ∀ n : ℕ, ∀ w : DirectionWord n,
    StoppedNetworkTrail p.normalized p.u (insert p.v (protectedSites p.G)) w →
    wordVertex p.u w n ∈ protectedSites p.G →
    let E := normalizeStart (traceNetwork p.normalized (wordVertices p.u w)) p.v p.c
    ∀ incoming : Compass, p.v = p.c + incoming.step → ∀ m : ℕ, ∀ w' : DirectionWord m,
      StoppedNetworkTrail E p.v (protectedSites p.G) w' → uncoveredCountV2 E p.v incoming w' ≤ 12

end AKLT.Blueprint.Rec
