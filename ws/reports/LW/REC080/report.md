STATUS: PROVED FROM DEPS

## Files

All Lean sources are under `AKLT/W/REC080/`:

| File | Role |
| --- | --- |
| `Main.lean` | Closed target theorem and discharge of both earlier residuals. |
| `Basic.lean` | Spin support bounds, nonnegative weights, and harmless normalization. |
| `Expansion.lean` | Absolute expectation bound from the second expansion. |
| `TerminalGeometry.lean` | Terminal start and target admissibility; erased arrival bond. |
| `Exceptions.lean` | Injectivity of U departures and the twelve-site diamond count. |
| `SharedCover.lean` | Shared-matcher covering away from the fixed terminal defect. |
| `Pointwise.lean` | Common pointwise trace-ratio majorant. |
| `Summation.lean` | Original protected-distance lower bound and geometric summation. |
| `Audit.lean` | Exact target-type check; types and axioms of all 81 exported theorems. |

The earlier helper proofs are reused. This completion changes `Main.lean` and
`Audit.lean`. No existing source outside REC080 was changed.

## Exported declarations

The requested declaration, with no residual arguments, is:

```lean
theorem AKLT.W.REC080.main :
    AKLT.Blueprint.Rec.ResidualTargetBoundStatement
```

Both residual propositions from the previous reduction are now proved:

```lean
theorem AKLT.W.REC080.secondExpansion :
    AKLT.W.REC080.ResidualSecondExpansion

theorem AKLT.W.REC080.coveredRatio :
    AKLT.W.REC080.ResidualCoveredRatio
```

`ResidualSecondExpansion` is the second finite pair-expansion identity in the
normalized terminal network, with stopping set exactly the original protected
set. `ResidualCoveredRatio` is definitionally
`AKLT.Blueprint.Rec.CoveredRatioStatementV2`.

The retained dependency reduction has type:

```lean
AKLT.Blueprint.Rec.PairExpansionStatement →
  AKLT.Blueprint.Rec.CoveredRatioStatementV2 →
  AKLT.Blueprint.Rec.ResidualTargetBoundStatement
```

It is exported as `AKLT.W.REC080.main_of_dependencies`. The exact types of all
81 exported theorems, and the four supporting definitions/structures, are
recorded in [audit.log](audit.log), produced by `Audit.lean`.

## Dependencies and proof

The two formerly open obligations are discharged using indexed proofs:

| Statement | Theorem | Module |
| --- | --- | --- |
| `AKLT.Blueprint.Rec.PairExpansionStatement` | `AKLT.W.REC043.main` | `AKLT.W.REC043.Main` |
| `AKLT.Blueprint.Rec.CoveredRatioStatementV2` | `AKLT.W.REC090.main` | `AKLT.W.REC090.Main` |

All imported blueprint leaves, including those already used by the helper
proofs, occur in the supplied proved index. The complete module/statement/theorem
inventory is [dependencies.tsv](dependencies.tsv).

The proof follows §7 lines 872–900. Harmless normalization preserves the
terminal expectation. The first erased arrival bond makes the protected target
admissible, including its original leg factors, so REC043 applies with stopping
set exactly S. Each residual scalar product has absolute expectation at most
one. The shared matcher localizes uncovered U departures to the punctured
radius-two diamond about the first terminal site; injectivity bounds their
number by twelve. REC090 supplies the covered local ratio estimate. The
pointwise maximum of the two pin-dependent ratios is bounded before summation.
Every second trail has length at least the original distance from v to S, and
H2 plus the geometric sum gives precisely
`onePointConstant CV q * q^(protectedDistance p.G p.v)`.

## Axioms

```text
#print axioms AKLT.W.REC080.main
'AKLT.W.REC080.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Audit.lean` ran `#print axioms` on every one of the 81 exported REC080 theorems.
Every reported axiom belongs to the allowed set
`{propext, Classical.choice, Quot.sound}`; full output is in
[audit.log](audit.log). The exact target type also passed an independent
`example : AKLT.Blueprint.Rec.ResidualTargetBoundStatement := AKLT.W.REC080.main`.
The forbidden-construct scan of all delivered Lean files had zero matches.

## Builds and timings

- `LEAN_NUM_THREADS=2 lake build AKLT.W.REC080.Main`: succeeded,
  8.987 s wall time; Lake reported 3.0 s for the module itself.
- `LEAN_NUM_THREADS=2 lake env lean AKLT/W/REC080/Audit.lean`: succeeded,
  4.469 s wall time.
- Newly needed indexed dependency artifacts were built first using single-module
  `lake build` calls. The ordered build driver, including the final main build,
  took 357.67 s. Independent dependency chains were also prepared concurrently;
  at most four Lean build processes were used.
- Mathlib was not rebuilt, and no package source was edited.

Full commands and outputs: [build.log](build.log),
[build-rec003.log](build-rec003.log), [build-rec089.log](build-rec089.log),
[build-rec090.log](build-rec090.log). Per-command timings are in
`build-timings.json`, `build-rec003-timings.json`,
`build-rec089-timings.json`, `build-rec090-timings.json`, and
`audit-timings.json`.

## Open issues

None. Both earlier residual propositions have proofs, and `main` has exactly
the requested closed statement type.

## ORCH-SUMMARY

- Delivered `AKLT/W/REC080/Main.lean` and its local helper files.
- Exact theorem: `AKLT.W.REC080.main : AKLT.Blueprint.Rec.ResidualTargetBoundStatement`.
- Status: PROVED FROM DEPS.
- Newly discharged dependencies: REC043 `PairExpansionStatement`; REC090 `CoveredRatioStatementV2`.
- Earlier residuals are proved as `secondExpansion` and `coveredRatio`.
- All imported blueprint leaves were verified against `proved-index.tsv`.
- Main build succeeded; complete 81-theorem type/axiom audit succeeded.
- Axioms of main: propext, Classical.choice, Quot.sound.
- Open declarations: none.
- Limitations or deviations: none; uses the user-authorized indexed dependencies.
- Orchestrator action: accept/register REC080; no further leaf handoff is needed.
