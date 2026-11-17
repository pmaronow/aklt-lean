STATUS: PROVED FROM DEPS

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC099/AKLT/W/REC099/Main.lean): the requested closed theorem, the twelve-offset enumeration, and injectivity of U departures. Reuses and completes the earlier attempt.
- [LocalCover.lean](/home/ubuntu/aklt/wt/LW_REC099/AKLT/W/REC099/LocalCover.lean): proves local coverage away from the protected terminal defect.
- [Audit.lean](/home/ubuntu/aklt/wt/LW_REC099/AKLT/W/REC099/Audit.lean): checks the exact requested type and prints the axioms of every public theorem.
- [exact-type.log](/home/ubuntu/aklt/reports/LW/REC099/exact-type.log): successful audit output and timing.

## Dependency and proof

Imports `AKLT.W.REC096.Main`, the indexed proved leaf for
`AKLT.Blueprint.Rec.CoveredClosureStatementV2`. Reuses its proved helper
library: `PrefixInvariant`, the first-trail prefix invariant, trace-step
preservation, geometry, and `invariant_covered`. No unproved blueprint leaf
is assumed.

Let `e` be the first trail's protected terminal. In the auxiliary proof,
remove `e` from the network's active sites without changing the original
volume or any kept set. Site removal commutes with tracing. The first
trail's final invariant, the second endpoint's unchanged status, and its
original D-degree bound establish the normalized second-start invariant
in this modified network.

For a second departure farther than two from `e`, all bonds through that
departure avoid `e`. A prefix induction therefore propagates the REC096
invariant through the required departure. REC096 supplies a covered
pattern. Every site of its radius-two template differs from `e`, so its
statuses and internal present bonds agree with the original network, and
the same pattern covers the actual departure. This argument does not
require the modified network to satisfy protected-site auxiliary laws.

Consequently, every uncovered U departure lies at positive distance at
most two from `e`. U departures at distinct indices have distinct sites,
because a departure changes U to D and tracing never creates U. Their
sites inject into the twelve explicitly enumerated offsets. This counts
exceptions at every position along the second trail.

The previous `Residual_terminalLocalCover` premise has been discharged
and removed. The requested `main` has no residual argument.

## Exported declarations and statements

The following signatures use `open AKLT.Defs AKLT.Blueprint.Rec` within
namespace `AKLT.W.REC099`.

`diamondOffsets : Finset Plane` is the set
`{(1,0), (0,1), (-1,0), (0,-1), (2,0), (0,2), (-2,0), (0,-2), (1,1), (1,-1), (-1,1), (-1,-1)}`.

```lean
lemma in_diamondOffsets {z e : Plane}
    (hpos : 0 < latticeDist z e) (hle : latticeDist z e ≤ 2) :
    ∃ d ∈ diamondOffsets, z = e + d

theorem uDepartureInjective :
    ∀ G : Finset Plane, ∀ D : Network G, ∀ u : Plane, ∀ T : Finset Plane,
      ∀ n : ℕ, ∀ w : DirectionWord n,
      StoppedNetworkTrail D u T w → ∀ i j : Fin n,
        (prefixNetwork D u w i.val).status (wordVertex u w i.val) = .U →
        (prefixNetwork D u w j.val).status (wordVertex u w j.val) = .U →
        wordVertex u w i.val = wordVertex u w j.val → i = j

theorem terminalLocalCover :
    ∀ p : PairSetup, p.v ∉ protectedSites p.G → ∀ n : ℕ, ∀ w : DirectionWord n,
      StoppedNetworkTrail p.normalized p.u (insert p.v (protectedSites p.G)) w →
      wordVertex p.u w n ∈ protectedSites p.G →
      let E := normalizeStart (traceNetwork p.normalized (wordVertices p.u w)) p.v p.c
      ∀ incoming : Compass, p.v = p.c + incoming.step → ∀ m : ℕ, ∀ w' : DirectionWord m,
        StoppedNetworkTrail E p.v (protectedSites p.G) w' → ∀ i : Fin m,
        (prefixNetwork E p.v w' i.val).status (wordVertex p.v w' i.val) = .U →
        2 < latticeDist (wordVertex p.v w' i.val) (wordVertex p.u w n) →
        AKLT.Defs.CoveredDepartureV2 (prefixNetwork E p.v w' i.val)
          (wordVertex p.v w' i.val) (wordIncoming incoming w' i) (w' i)

theorem main : AKLT.Blueprint.Rec.TerminalExceptionCountStatementV2
```

All other proof helpers in REC099 are private.

## Axioms and exact-type check

The audit succeeded with this output:

```text
AKLT.W.REC099.main : AKLT.Blueprint.Rec.TerminalExceptionCountStatementV2
'AKLT.W.REC099.in_diamondOffsets' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC099.uDepartureInjective' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC099.terminalLocalCover' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC099.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No forbidden proof constructs or additional axioms are used.

## Build commands and timings

Run in `/home/ubuntu/aklt/wt/LW_REC099`, with `$HOME/.elan/bin` on `PATH`:

- `lake build AKLT.W.REC099.Main` — passed, 8971 jobs. Lake reported 11 s for `AKLT.W.REC099.LocalCover` and 21 s for `AKLT.W.REC099.Main`. The REC096 dependency modules had been built during the preceding helper build; no dependency sources were edited.
- `/usr/bin/time -p lake env lean AKLT/W/REC099/Audit.lean` — passed; real 10.09 s, user 4.81 s, sys 3.13 s. The audit checks `(AKLT.W.REC099.main : AKLT.Blueprint.Rec.TerminalExceptionCountStatementV2)` explicitly.
- `git diff --check` — passed. Worktree source changes are confined to `AKLT/W/REC099/`.

## Open issues

None. The exact requested closed theorem is proved using the indexed REC096 library.

## ORCH-SUMMARY

- Delivered `AKLT.W.REC099.main : AKLT.Blueprint.Rec.TerminalExceptionCountStatementV2`.
- STATUS: PROVED FROM DEPS; indexed dependency: `AKLT.W.REC096.Main` and its proved helpers.
- Closed the earlier local-cover residual with `AKLT.W.REC099.terminalLocalCover`.
- The count covers all exceptional indices, with no prefix restriction.
- Added `LocalCover.lean` and `Audit.lean`; completed the existing task-local `Main.lean`.
- Exact-type audit and `lake build AKLT.W.REC099.Main` both pass.
- Every public theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.
- No open leaves, residual premises, limitations, or specification deviations.
- No orchestrator decision is required; REC099 is ready for acceptance.
