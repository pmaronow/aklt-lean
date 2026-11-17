STATUS: PARTIAL

The requested unconditional theorem is not proved. The compiled declaration
`AKLT.W.REC095.main` has the explicit type
`Residual_CoveredRatio → AKLT.Blueprint.Rec.OnePointSumStatementV2`.
The only remaining premise of this declaration is exactly the open blueprint
leaf `AKLT.Blueprint.Rec.CoveredRatioStatementV2` (REC090).

The earlier attempt stopped at `OnePointPointwiseStatementV2` (REC094).
This delivery proves that pointwise leaf from REC090, using the proved leaves
REC010, REC011, REC012, REC013, REC039, and REC041 from the supplied index.
It also proves that `LocalMixtureStatementV2` (REC089) suffices to discharge
REC090. Neither REC089 nor REC090 is assumed to have been proved.

## Files

All source files are in `/home/ubuntu/aklt/wt/LW_REC095/AKLT/W/REC095/`.
No frozen statement or source outside this directory was edited.

| File | Content |
| --- | --- |
| [Main.lean](/home/ubuntu/aklt/wt/LW_REC095/AKLT/W/REC095/Main.lean) | Retained geometry, finite length grouping, and geometric tail; new conditional `main` and `main_of_localMixture`. |
| [Pointwise.lean](/home/ubuntu/aklt/wt/LW_REC095/AKLT/W/REC095/Pointwise.lean) | New proof of the pointwise leaf from the single covered-ratio residual. |
| [Local.lean](/home/ubuntu/aklt/wt/LW_REC095/AKLT/W/REC095/Local.lean) | New proof that the local mixture leaf implies the covered-ratio residual. |
| [Trace.lean](/home/ubuntu/aklt/wt/LW_REC095/AKLT/W/REC095/Trace.lean) | Departure coefficients and revisit status facts; reuses the proved REC039 trace dynamics. |
| [Positivity.lean](/home/ubuntu/aklt/wt/LW_REC095/AKLT/W/REC095/Positivity.lean) | Retained earlier positivity helpers; compiled and audited, but not needed by `main`. |
| [Audit.lean](/home/ubuntu/aklt/wt/LW_REC095/AKLT/W/REC095/Audit.lean) | Types and axiom audits for every exported theorem, plus successful conditional type checks. |

## Residual and reduction

The sole unresolved input used by `main` is the following closed, transparent
statement, substantially smaller than the stopped-trail sum:

```lean
-- In namespace AKLT.W.REC095, with AKLT.Defs and AKLT.Blueprint.Rec open:
def Residual_CoveredRatio : Prop := CoveredRatioStatementV2

-- Expanded:
AKLT.Blueprint.Top.H1Statement →
  ∀ a : Departure, a.D.status a.y = .U →
  ∀ incoming outgoing : Compass, a.o = a.y + outgoing.step →
    AKLT.Defs.CoveredDepartureV2 a.D a.y incoming outgoing →
      stepRatio a.D a.τ true a.y a.o ≤
        (passageFactor (decide (outgoing = incoming)) : ℝ)
```

The retained `Residual_OnePointPointwise` is an alias of
`OnePointPointwiseStatementV2`; it is now derived from
`Residual_CoveredRatio` by `pointwise_of_coveredRatio`.
The retained `Residual_StoppedTrailGeometry` states that every stopped trail,
with its absent designated incoming bond, is an `IsTrail` and has length at
least `protectedDistance G u`. It is proved unconditionally by
`stoppedTrailGeometry`, so it is not an open issue.

For each departure, the pointwise proof combines the evolving coefficient
with its step ratio. Covered U departures use REC090; other U departures
use the uniform factor 12/5. A revisited site cannot have status U, and D
steps have ratio one. The common product majorant for both pin choices is
`(12/5)^(uncoveredCountV2 D u incoming w) * trailWeight u incoming w`.
Monotonicity of powers applies the twelve-exception bound before taking
the maximum.

The sum proof keeps the identical incoming direction when enlarging each
length class into the H2 class. The absent incoming bond excludes the first
reversal. Every stopped trail reaches the original protected layer, giving
the required lower bound on length. Finite length grouping and the
q-geometric tail then give precisely the frozen constant and exponent.
The alternative mixture implication applies H1 term by term with common
nonnegative weights and divides by the proved positive current partition.

## Exported declarations and statements

The following is the actual `#check` output for every exported definition
and theorem in the delivered files. The three residual definitions are
explicit statements, not axioms.

```text
AKLT.W.REC095.departureCoefficient (s : AKLT.Defs.Status) : ℚ
AKLT.W.REC095.departureCoefficient_nonneg (s : AKLT.Defs.Status) : 0 ≤ AKLT.W.REC095.departureCoefficient s
AKLT.W.REC095.present_neighbour {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} {x y : AKLT.Defs.Plane}
  (hD : D.LocalRules) (h : D.Present x y) : y ∈ D.presentNeighbours x
AKLT.W.REC095.revisit_status_ne_U {G : Finset AKLT.Defs.Plane} {n : ℕ} (D : AKLT.Defs.Network G) (u : AKLT.Defs.Plane)
  (w : AKLT.Defs.DirectionWord n) (i : Fin n) (hi : AKLT.Defs.wordRevisit u w i = true) :
  (AKLT.Blueprint.Rec.prefixNetwork D u w ↑i).status (AKLT.Defs.wordVertex u w ↑i) ≠ AKLT.Defs.Status.U
AKLT.W.REC095.traceDynamics : AKLT.Blueprint.Rec.TraceDynamicsStatement
AKLT.W.REC095.icoVector_normSq (j : AKLT.Defs.IcoLetter) : AKLT.Defs.normSq (AKLT.Defs.icoVector j) = 1
AKLT.W.REC095.normSq_nonneg (v : AKLT.Defs.Vec3) : 0 ≤ AKLT.Defs.normSq v
AKLT.W.REC095.normSq_zero : AKLT.Defs.normSq 0 = 0
AKLT.W.REC095.dot_ge_neg_one {a b : AKLT.Defs.Vec3} (ha : AKLT.Defs.normSq a ≤ 1) (hb : AKLT.Defs.normSq b ≤ 1) :
  -1 ≤ AKLT.Defs.dot a b
AKLT.W.REC095.spinVector_normSq_le (s : AKLT.Defs.SpinLetter) : AKLT.Defs.normSq (AKLT.Defs.spinVector s) ≤ 1
AKLT.W.REC095.spinWeight_nonneg (s : AKLT.Defs.Status) (j : AKLT.Defs.SpinLetter) : 0 ≤ AKLT.Defs.spinWeight s j
AKLT.W.REC095.spins_normSq_le {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (σ : ↥D.active → AKLT.Defs.SpinLetter) (x : AKLT.Defs.Plane) : AKLT.Defs.normSq (D.spins σ x) ≤ 1
AKLT.W.REC095.partition_nonneg {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) : 0 ≤ D.partition τ b fun x => 1
AKLT.W.REC095.Residual_CoveredRatio : Prop
AKLT.W.REC095.traceCoefficient_product {G : Finset AKLT.Defs.Plane} {n : ℕ} (D : AKLT.Defs.Network G)
  (u : AKLT.Defs.Plane) (w : AKLT.Defs.DirectionWord n) :
  AKLT.Defs.traceCoefficient D (AKLT.Defs.wordVertices u w) =
    ∏ i,
      AKLT.W.REC095.departureCoefficient
        ((AKLT.Blueprint.Rec.prefixNetwork D u w ↑i).status (AKLT.Defs.wordVertex u w ↑i))
AKLT.W.REC095.pointwise_of_coveredRatio (hcovered : AKLT.W.REC095.Residual_CoveredRatio) :
  AKLT.Blueprint.Rec.OnePointPointwiseStatementV2
AKLT.W.REC095.coveredRatio_of_localMixture (hmixture : AKLT.Blueprint.Rec.LocalMixtureStatementV2) :
  AKLT.W.REC095.Residual_CoveredRatio
AKLT.W.REC095.Residual_OnePointPointwise : Prop
AKLT.W.REC095.Residual_StoppedTrailGeometry : Prop
AKLT.W.REC095.stoppedTrailGeometry : AKLT.W.REC095.Residual_StoppedTrailGeometry
AKLT.W.REC095.main_of_residuals (hpoint : AKLT.W.REC095.Residual_OnePointPointwise)
  (hgeo : AKLT.W.REC095.Residual_StoppedTrailGeometry) : AKLT.Blueprint.Rec.OnePointSumStatementV2
AKLT.W.REC095.main_of_pointwise (hpoint : AKLT.W.REC095.Residual_OnePointPointwise) :
  AKLT.Blueprint.Rec.OnePointSumStatementV2
AKLT.W.REC095.main (hcovered : AKLT.W.REC095.Residual_CoveredRatio) : AKLT.Blueprint.Rec.OnePointSumStatementV2
AKLT.W.REC095.main_of_localMixture (hmixture : AKLT.Blueprint.Rec.LocalMixtureStatementV2) :
  AKLT.Blueprint.Rec.OnePointSumStatementV2
```

## Axiom audit

`Audit.lean` runs `#print axioms` on every exported theorem. Actual output:

```text
'AKLT.W.REC095.departureCoefficient_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC095.present_neighbour' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC095.revisit_status_ne_U' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC095.traceDynamics' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC095.icoVector_normSq' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC095.normSq_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC095.normSq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC095.dot_ge_neg_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC095.spinVector_normSq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC095.spinWeight_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC095.spins_normSq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC095.partition_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC095.traceCoefficient_product' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC095.pointwise_of_coveredRatio' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC095.coveredRatio_of_localMixture' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC095.stoppedTrailGeometry' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC095.main_of_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC095.main_of_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC095.main' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC095.main_of_localMixture' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only the permitted axioms `propext`, `Classical.choice`, and `Quot.sound`
appear. A source scan found none of the prohibited proof escapes.

## Build and exact-type validation

Commands ran with `PATH="$HOME/.elan/bin:$PATH"`; wall times below were
measured with `/usr/bin/time -p`.

| Command | Result | Wall time |
| --- | --- | --- |
| `lake build AKLT.W.REC095.Main` | Successful full build of the final proof modules | 23.74 s |
| `lake build AKLT.W.REC095.Main` | Successful final verification | 4.33 s |
| `lake build AKLT.W.REC095.Audit` | Successful; all six source files compile and all theorem audits pass | 15.87 s |
| `lake env lean /tmp/rec095-exact-check.lean` | Expected failure: unconditional type still requires REC090 | 4.44 s |

The successful audit includes explicit examples checking
`Residual_CoveredRatio → OnePointSumStatementV2` and
`LocalMixtureStatementV2 → OnePointSumStatementV2`.
The unconditional check is deliberately reported as failed:

```text
/tmp/rec095-exact-check.lean:2:55: error: Type mismatch
  AKLT.W.REC095.main
has type
  AKLT.W.REC095.Residual_CoveredRatio → AKLT.Blueprint.Rec.OnePointSumStatementV2
but is expected to have type
  AKLT.Blueprint.Rec.OnePointSumStatementV2
'AKLT.W.REC095.main' depends on axioms: [propext, Classical.choice, Quot.sound]
real 4.44
user 3.00
sys 1.46
```

Logs: [build-main.log](build-main.log), [build-audit.log](build-audit.log),
[exact-type-check.log](exact-type-check.log), [declarations.log](declarations.log),
and [axioms.log](axioms.log).

## Open issue

Exactly one local leaf is required by the primary reduction:
`AKLT.Blueprint.Rec.CoveredRatioStatementV2` (REC090).
What remains unproved is the transfer from H1 on full covered patterns to
an actual auxiliary-network departure with the shared matcher. This requires
the local conditioning, tip replacement, and external-slot resolution bridge.
`coveredRatio_of_localMixture` proves that the existing closed leaf
`AKLT.Blueprint.Rec.LocalMixtureStatementV2` (REC089) is sufficient for this
bridge, but does not construct that mixture.

No counterexample or missing hypothesis has been established. The limitation
is an unfinished local analytic proof, and the requested exact unconditional
`AKLT.W.REC095.main` is not delivered. REC094 can also be used directly via
the retained `main_of_pointwise` once it is proved.

## ORCH-SUMMARY

- STATUS: PARTIAL.
- Compiled reduction: `AKLT.W.REC095.main : Residual_CoveredRatio → OnePointSumStatementV2`.
- Exact remaining leaf: `AKLT.Blueprint.Rec.CoveredRatioStatementV2` (REC090).
- `pointwise_of_coveredRatio` proves REC094 from REC090; no separate trace-product residual remains.
- Alternative sufficient leaf: `AKLT.Blueprint.Rec.LocalMixtureStatementV2` (REC089).
- `coveredRatio_of_localMixture` and `main_of_localMixture` prove that alternative reduction.
- Trail geometry, fixed-incoming H2 inclusion, finite grouping, and geometric tail are proved.
- Reused proved leaves: REC010, REC011, REC012, REC013, REC039, REC041.
- All six source modules compile; every exported theorem has a permitted-axiom audit.
- Main and audit builds pass; the unconditional exact-type check fails on the explicit residual premise.
- No frozen or other-task source was edited; no sub-agents were used.
- No false-statement claim or counterexample is made.
- Orchestrator: finish REC090 (or REC089), then apply the supplied reduction to obtain the closed REC095 theorem.
