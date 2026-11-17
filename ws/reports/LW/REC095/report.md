STATUS: PROVED FROM DEPS

Delivered the exact requested declaration, with no residual premise:

```lean
theorem AKLT.W.REC095.main : AKLT.Blueprint.Rec.OnePointSumStatementV2 :=
  AKLT.W.REC095.main_of_pointwise AKLT.W.REC094.main
```

The supplied proved-leaf index authorizes `AKLT.W.REC094.main` from
`AKLT.W.REC094.Main`, proving `AKLT.Blueprint.Rec.OnePointPointwiseStatementV2`.
Its covered-ratio dependency REC090 and mixture dependency REC089 are also
present in that index. This completes the earlier reduction without assuming
any unproved leaf.

## Files

All Lean sources are under `/home/ubuntu/aklt/wt/LW_REC095/AKLT/W/REC095/`.

| File | Delivered content |
| --- | --- |
| [Main.lean](/home/ubuntu/aklt/wt/LW_REC095/AKLT/W/REC095/Main.lean) | Reused stopped-trail geometry, finite grouping, and geometric tail. Imports REC094 and closes the exact `main`. The earlier conditional `main` is retained as `main_of_coveredRatio`. |
| [Audit.lean](/home/ubuntu/aklt/wt/LW_REC095/AKLT/W/REC095/Audit.lean) | Exact requested type check and `#print axioms` on all 21 exported theorems in the six source files. |
| [Local.lean](/home/ubuntu/aklt/wt/LW_REC095/AKLT/W/REC095/Local.lean) | Retained earlier local-mixture-to-covered-ratio implication. |
| [Pointwise.lean](/home/ubuntu/aklt/wt/LW_REC095/AKLT/W/REC095/Pointwise.lean) | Retained earlier conditional pointwise proof and coefficient product identity. |
| [Trace.lean](/home/ubuntu/aklt/wt/LW_REC095/AKLT/W/REC095/Trace.lean) | Retained departure and revisit facts, using indexed REC039. |
| [Positivity.lean](/home/ubuntu/aklt/wt/LW_REC095/AKLT/W/REC095/Positivity.lean) | Retained positivity helpers, compiled and audited. |

Only `Main.lean` and `Audit.lean` were changed in this completion. No frozen
statement or source outside REC095 was edited. No sub-agents were used.

## Proof

A stopped trail already has distinct unoriented bonds. Symmetry of present
bonds and the absent incoming bond forbid its initial reversal, so it is an
H2 trail with the identical incoming direction. Its endpoint belongs to the
original `protectedSites G`; ambient lattice distance is at most its length.
This also supplies a finite distance bound whenever such a trail exists.

REC094 bounds each summand, including the maximum over pin choices, by
`exceptionFactor * trailWeight`. For each fixed length, nonnegative weights
permit enlarging the stopped-trail class to the H2 class. Lengths below
`protectedDistance G u` have no stopped trails. Grouping the finite sum by
length and bounding its finite geometric tail by `q^d / (1-q)` gives precisely
`onePointConstant CV q * q^(protectedDistance G u)`.

The historical transparent definitions `Residual_OnePointPointwise`,
`Residual_CoveredRatio`, and `Residual_StoppedTrailGeometry` remain as helper
interfaces. They impose no additional premise on `main`: REC094 proves the
pointwise input, REC090 proves the covered-ratio input, and
`stoppedTrailGeometry` proves the geometry input directly. There are no open
residual statements.

## Exported declarations and statements

Actual `#check` output for every exported definition and theorem in the
REC095 source files:

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
AKLT.W.REC095.main_of_coveredRatio (hcovered : AKLT.W.REC095.Residual_CoveredRatio) :
  AKLT.Blueprint.Rec.OnePointSumStatementV2
AKLT.W.REC095.main : AKLT.Blueprint.Rec.OnePointSumStatementV2
AKLT.W.REC095.main_of_localMixture (hmixture : AKLT.Blueprint.Rec.LocalMixtureStatementV2) :
  AKLT.Blueprint.Rec.OnePointSumStatementV2
```

## Axiom audit

Actual `#print axioms` output for every exported theorem:

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
'AKLT.W.REC095.main_of_coveredRatio' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC095.main' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC095.main_of_localMixture' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All outputs use only the permitted axioms `propext`, `Classical.choice`, and
`Quot.sound`. A source scan found none of the prohibited proof escapes.

## Build and exact-type verification

Commands ran with `PATH="$HOME/.elan/bin:$PATH"`; `/usr/bin/time` measured
wall times. The audit build used `LEAN_NUM_THREADS=4`.

| Command | Result | Wall time |
| --- | --- | --- |
| `lake build AKLT.W.REC095.Main` | Passed, including compilation of newly imported proved dependencies | 80.29 s |
| `lake build AKLT.W.REC095.Audit` | Passed, including all exported theorem audits and the unconditional type check | 8.60 s |
| `lake env lean /tmp/rec095-exact-check.lean` | Passed independently, importing only `AKLT.W.REC095.Main` | 4.16 s |

The standalone check contains:

```lean
import AKLT.W.REC095.Main
example : AKLT.Blueprint.Rec.OnePointSumStatementV2 := AKLT.W.REC095.main
#check (AKLT.W.REC095.main : AKLT.Blueprint.Rec.OnePointSumStatementV2)
#print axioms AKLT.W.REC095.main
```

Its output is:

```text
AKLT.W.REC095.main : AKLT.Blueprint.Rec.OnePointSumStatementV2
'AKLT.W.REC095.main' depends on axioms: [propext, Classical.choice, Quot.sound]
elapsed_seconds=4.16
```

Logs: [build-main.log](build-main.log), [build-audit.log](build-audit.log),
[exact-type-check.log](exact-type-check.log), [declarations.log](declarations.log),
and [axioms.log](axioms.log). Build output includes existing linter warnings;
there were no errors.

## Open issues

None. The exact theorem name and type are delivered. The result uses the
newly authorized indexed REC094 proof; it has no additional assumptions
beyond the frozen statement's hypotheses.

## ORCH-SUMMARY

- STATUS: PROVED FROM DEPS.
- Delivered `AKLT.W.REC095.main : AKLT.Blueprint.Rec.OnePointSumStatementV2`.
- Primary authorized dependency: `AKLT.W.REC094.main` (`AKLT.W.REC094.Main`).
- REC094's REC090 and REC089 dependencies are also in the supplied index.
- Reused the earlier geometry, fixed-incoming H2 inclusion, finite grouping, and geometric tail.
- The earlier conditional `main` is now `main_of_coveredRatio`; exact `main` has no residual premise.
- Historical residual definitions remain only as proved/helper interfaces; none is open.
- Main build, all-source audit build, and independent exact-type check passed.
- All 21 exported theorem axiom audits contain only propext, Classical.choice, Quot.sound.
- Changed only REC095/Main.lean, REC095/Audit.lean, and report artifacts.
- No frozen definitions changed; no prohibited escapes; no sub-agents.
- Limitations or deviations: none; dependency reuse is explicitly authorized.
- Open names: none. Orchestrator can accept REC095 as proved from indexed dependencies.
