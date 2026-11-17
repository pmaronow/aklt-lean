module
public import AKLT.Blueprint.Rec.NodesWalk

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.Blueprint.Rec

/-- `l:closure`, §7 lines 88–104. Erasing a flag to the removed center
changes no present bond, site law, leg, partition, or expectation. -/
def NormalizeStartStatement : Prop :=
  ∀ p : PairData, p.normalized.bonds = p.D.bonds ∧
    ∀ b : Bool, ∀ f : (Plane → Vec3) → ℝ,
      p.normalized.partition p.τ b f = p.D.partition p.τ b f

/-- `l:closure`, §7 lines 106–132. Strengthened prefix invariant. Only
the live site can violate the full-U/two-kept-D rules; active kept flags
remain mutual. A previously departed site is never U again. -/
def KeptInvariantStatement : Prop :=
  ∀ p : PairSetup, ∀ T : Finset Plane, ∀ n : ℕ, ∀ w : DirectionWord n,
    StoppedNetworkTrail p.normalized p.u T w → ∀ j ≤ n,
    let E := prefixNetwork p.normalized p.u w j
    let y := wordVertex p.u w j
    E.Auxiliary ∧
    (∀ x ∈ p.G, x ≠ y → E.status x = .U → E.kept x = neighbors x ∩ p.G) ∧
    (∀ x ∈ p.G, x ≠ y → E.status x = .D → (E.kept x).card = 2) ∧
    (∀ x ∈ E.active, ∀ z ∈ E.active, Adjacent x z → (z ∈ E.kept x ↔ x ∈ E.kept z)) ∧
    (∀ i < j, E.status (wordVertex p.u w i) ≠ .U)

/-- `l:closure`, §7 lines 133–145. Removing the live interior endpoint
removes the sole ordinary kept-set defect; do not remove a protected terminal. -/
def RemovedClosureStatement : Prop :=
  ∀ p : PairSetup, ∀ T : Finset Plane, ∀ n : ℕ, ∀ w : DirectionWord n,
    StoppedNetworkTrail p.normalized p.u T w → ∀ j ≤ n,
    wordVertex p.u w j ∉ protectedSites p.G →
      (removeSite (prefixNetwork p.normalized p.u w j) (wordVertex p.u w j)).Consistent

/-- `l:closure`, §7 lines 147–158. Check central, arrival, three
nonarrival neighbors and four corners. V2 compares inside-G flags and
permits the original-leg slots at boundary corners; tips remain covering U. -/
def CoveredClosureStatement : Prop :=
  ∀ p : PairSetup, ∀ T : Finset Plane, ∀ n : ℕ, ∀ w : DirectionWord n,
    StoppedNetworkTrail p.normalized p.u T w → ∀ i : Fin n,
    (prefixNetwork p.normalized p.u w i.val).status (wordVertex p.u w i.val) = .U →
      CoveredDepartureV2 (prefixNetwork p.normalized p.u w i.val) (wordVertex p.u w i.val)
        (wordIncoming p.incoming w i) (w i)

/-- `l:closure`, §7 lines 159–166. The response endpoints keep their
bonds to the live U site. After deletion D endpoints have degree≤1. -/
def PairClosureStatement : Prop :=
  ∀ p : PairSetup, ∀ T : Finset Plane, ∀ n : ℕ, ∀ w : DirectionWord n,
    StoppedNetworkTrail p.normalized p.u T w → ∀ i : Fin n,
    let E := prefixNetwork p.normalized p.u w i.val
    let y := wordVertex p.u w i.val
    E.status y = .U → ∀ a ∈ E.presentNeighbors y, ∀ b ∈ E.presentNeighbors y, a ≠ b →
      (removeSite E y).ResponsePair (responsePairType {a, b}) a b y

/-- `l:closure`, §7 lines 139–145. The terminal hit in S retains its U
law and all legs; it alone can have an incomplete protected kept set. -/
def TerminalDefectStatement : Prop :=
  ∀ p : PairSetup, ∀ n : ℕ, ∀ w : DirectionWord n,
    StoppedNetworkTrail p.normalized p.u (protectedSites p.G) w →
    let E := traceNetwork p.normalized (wordVertices p.u w)
    let e := wordVertex p.u w n
    E.Auxiliary ∧ E.status e = .U ∧
      ∀ x ∈ protectedSites p.G, x ≠ e → E.kept x = neighbors x ∩ p.G

/-- `l:terminalcover`, §7 lines 183–210. BOTH endpoints must be outside S.
After the first trail avoids v and stops in S, the normalized second start
is admissible, has an absent incoming bond, and its target has at most three
incident factors including unchanged original legs. -/
def SecondStartStatement : Prop :=
  ∀ p : PairSetup, p.v ∉ protectedSites p.G → ∀ n : ℕ, ∀ w : DirectionWord n,
    StoppedNetworkTrail p.normalized p.u (insert p.v (protectedSites p.G)) w →
    wordVertex p.u w n ∈ protectedSites p.G →
    let E := normalizeStart (traceNetwork p.normalized (wordVertices p.u w)) p.v p.c
    E.Auxiliary ∧ E.AdmissibleStart p.v ∧ ¬ E.Present p.c p.v ∧
      AdmissibleTarget E (wordVertex p.u w n)

/-- `l:terminalcover`, §7 lines 212–240. Repeat the prefix invariant
with one fixed protected defect e. Every uncovered U departure is within
distance one or two of e, at any position along the second trail. -/
def TerminalExceptionLocationStatement : Prop :=
  ∀ p : PairSetup, p.v ∉ protectedSites p.G → ∀ n : ℕ, ∀ w : DirectionWord n,
    StoppedNetworkTrail p.normalized p.u (insert p.v (protectedSites p.G)) w →
    wordVertex p.u w n ∈ protectedSites p.G →
    let E := normalizeStart (traceNetwork p.normalized (wordVertices p.u w)) p.v p.c
    ∀ incoming : Compass, p.v = p.c + incoming.step → ∀ m : ℕ, ∀ w' : DirectionWord m,
      StoppedNetworkTrail E p.v (protectedSites p.G) w' → ∀ i : Fin m,
      (prefixNetwork E p.v w' i.val).status (wordVertex p.v w' i.val) = .U →
      ¬ CoveredDepartureV2 (prefixNetwork E p.v w' i.val) (wordVertex p.v w' i.val)
        (wordIncoming incoming w' i) (w' i) →
      0 < latticeDist (wordVertex p.v w' i.val) (wordVertex p.u w n) ∧
        latticeDist (wordVertex p.v w' i.val) (wordVertex p.u w n) ≤ 2

/-- `l:terminalcover`, §7 lines 233–240. A U departure is the only U
departure at that vertex. Use the status transition U→D→X. -/
def UDepartureInjectiveStatement : Prop :=
  ∀ G : Finset Plane, ∀ D : Network G, D.Auxiliary → ∀ u : Plane,
    D.AdmissibleStart u → ∀ T : Finset Plane, ∀ n : ℕ, ∀ w : DirectionWord n,
    StoppedNetworkTrail D u T w → ∀ i j : Fin n,
    (prefixNetwork D u w i.val).status (wordVertex u w i.val) = .U →
    (prefixNetwork D u w j.val).status (wordVertex u w j.val) = .U →
    wordVertex u w i.val = wordVertex u w j.val → i = j

/-- `l:terminalcover`, §7 lines 233–240. Four sites at distance one and
eight at distance two; prove by translation and a fixed 5×5 enumeration. -/
def DiamondTwelveStatement : Prop :=
  ∀ e : Plane, ((square e 2).filter fun z => 0 < latticeDist z e ∧ latticeDist z e ≤ 2).card = 12

/-- `l:terminalcover`, §7 lines 233–244. Inject exceptional U indices
into the twelve-site punctured diamond. No prefix-only exception assumption. -/
def TerminalExceptionCountStatement : Prop :=
  ∀ p : PairSetup, p.v ∉ protectedSites p.G → ∀ n : ℕ, ∀ w : DirectionWord n,
    StoppedNetworkTrail p.normalized p.u (insert p.v (protectedSites p.G)) w →
    wordVertex p.u w n ∈ protectedSites p.G →
    let E := normalizeStart (traceNetwork p.normalized (wordVertices p.u w)) p.v p.c
    ∀ incoming : Compass, p.v = p.c + incoming.step → ∀ m : ℕ, ∀ w' : DirectionWord m,
      StoppedNetworkTrail E p.v (protectedSites p.G) w' → uncoveredCount E p.v incoming w' ≤ 12

end AKLT.Blueprint.Rec
