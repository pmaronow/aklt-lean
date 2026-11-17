STATUS: PARTIAL

## Delivered result

The closed theorem `AKLT.W.REC080.main : AKLT.Blueprint.Rec.ResidualTargetBoundStatement` remains open. No theorem named `main` with extra hypotheses is presented as the requested result.

The compiled reduction now needs exactly these two unproved blueprint leaves, both absent from `/home/ubuntu/aklt/state/lw/proved-index.tsv`:

1. `AKLT.Blueprint.Rec.PairExpansionStatement` — the finite pair-walk expansion.
2. `AKLT.Blueprint.Rec.CoveredRatioStatementV2` — H1 implies the one-step ratio bound using the shared present-bond matcher.

All terminal admissibility, auxiliary-network invariants, shared-matcher exception localization/counting, finite-product comparisons, and H2 geometric summation are discharged. In particular, no terminal-tail or terminal-trace-majorant premise remains.

## Files

All Lean changes are confined to `AKLT/W/REC080/`.

- `Main.lean`: two transparent residual definitions and the conditional assembly.
- `SharedCover.lean` (new): auxiliary preservation, the moving-endpoint/fixed-protected-defect invariant, and proofs of both shared terminal-exception blueprint statements.
- `Pointwise.lean` (new): coefficient product formula, U implies lattice first visit, and the pointwise one-point bound from the shared local ratio comparison.
- `Basic.lean`, `Expansion.lean`, `Summation.lean`, `TerminalGeometry.lean`, `Exceptions.lean`: retained useful proofs from the previous attempt.
- `Audit.lean` (new): exact conditional-type checks and `#check`/`#print axioms` for every one of the 78 exported theorems.

The original report is retained as `report.luna.md`. Verification artifacts are `build.log`, `build-time.txt`, `audit.log`, and `audit-time.txt` in this report directory.

## Exported declarations and statements

All names below have prefix `AKLT.W.REC080`. The complete types of all 78 exported theorems, including every helper, are recorded by Lean in [audit.log](audit.log).

```lean
terminal_exception_location :
  AKLT.Blueprint.Rec.TerminalExceptionLocationStatementV2

terminal_exception_count :
  AKLT.Blueprint.Rec.TerminalExceptionCountStatementV2

onePointPointwise_of_coveredRatio :
  AKLT.Blueprint.Rec.CoveredRatioStatementV2 →
  AKLT.Blueprint.Rec.OnePointPointwiseStatementV2

secondExpansion_of_pairwalk :
  AKLT.Blueprint.Rec.PairExpansionStatement → ResidualSecondExpansion

main_of_residuals :
  ResidualSecondExpansion → ResidualCoveredRatio →
  AKLT.Blueprint.Rec.ResidualTargetBoundStatement

main_of_dependencies :
  AKLT.Blueprint.Rec.PairExpansionStatement →
  AKLT.Blueprint.Rec.CoveredRatioStatementV2 →
  AKLT.Blueprint.Rec.ResidualTargetBoundStatement
```

`ResidualSecondExpansion : Prop` explicitly states the finite expansion in the normalized terminal auxiliary network, from `p.v` to the first protected hit `e`, stopping at exactly the original `protectedSites p.G`. It is an identity with no H1, H2, or geometric-decay conclusion. Its full definition is printed at the start of `audit.log`.

`ResidualCoveredRatio : Prop` explicitly states the local one-step H1 comparison. It is definitionally equal to `AKLT.Blueprint.Rec.CoveredRatioStatementV2`; `Audit.lean` checks this equality by `rfl`. It uses `AKLT.Defs.CoveredDepartureV2`, not the frozen Rec-local intersection matcher.

`terminal_auxiliary`, `terminal_start_admissible`, `terminal_target_admissible`, and `terminal_shared_exception_bound` discharge every network/geometry premise used to instantiate the expansion and one-point estimates. `terminal_expansion_bound` bounds the second expansion by `onePointSum` given only the expansion residual. `terminal_tail_bound` proves

```lean
onePointSum (terminalNetwork p w) p.τ p.v ≤
  onePointConstant CV q * q ^ protectedDistance p.G p.v
```

under `ResidualCoveredRatio`, H1, H2, and the original first-trail hypotheses.

## Proof details

The normalized second network is auxiliary by the proved terminal-defect leaf and harmless flag erasure. The first lost arrival bond gives the protected target total incident-factor degree at most three, including original legs.

The second walk preserves an invariant allowing two kept-set defects: its live endpoint and the fixed first protected hit `e`. At a U departure more than distance two from `e`, temporarily removing `e` gives a comparison network satisfying the proved REC096 prefix invariant. Its extracted shared cover transfers back because all template sites are within distance two of the departure. Thus uncovered U departures lie in the punctured radius-two diamond. U departure indices are injective at their vertices, giving the bound twelve at arbitrary positions along the second walk.

The coefficient and ratio telescope into per-departure products. Covered U steps use only `ResidualCoveredRatio`; uncovered U steps cost at most `12/5`; D steps have ratio one. A true U departure is a lattice first visit, while an initially D first visit only reduces the weight. This proves the common pointwise maximum bound with `(12/5)^12`. Summing over lengths uses the original protected distance from `p.v`, H2 with a single fixed incoming direction, and the geometric tail. The maximum stays inside the finite sum.

Imported proved leaves are REC011, REC012, REC013, REC039, REC041, REC054, and REC096, all listed in the supplied proved index. No unindexed blueprint leaf is used as an established fact.

## Axiom audit

The audit succeeded for all 78 exported theorems. Every axiom is among `propext`, `Classical.choice`, and `Quot.sound`. The complete output is in [audit.log](audit.log). In particular:

```text
'AKLT.W.REC080.terminal_exception_location' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC080.terminal_exception_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC080.onePointPointwise_of_coveredRatio' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC080.main_of_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC080.main_of_dependencies' depends on axioms: [propext, Classical.choice, Quot.sound]
```

A source scan found none of the forbidden proof mechanisms.

## Build and checks

Commands ran with `PATH="$HOME/.elan/bin:$PATH"`:

- `lake build AKLT.W.REC080.Main` — succeeded; final measured build 21.44 seconds. It rebuilt `SharedCover` (5.7 s), `Pointwise` (7.1 s), and `Main` (3.0 s). No warnings originate in the final REC080 files; existing imported leaves emit their own warnings.
- `lake env lean AKLT/W/REC080/Audit.lean` — succeeded; 4.54 seconds. It checks the exact conditional reduction type, the residual/local-leaf definitional equality, and all 78 theorem axiom sets.

## Open issues

- `AKLT.Blueprint.Rec.PairExpansionStatement`: still requires the general finite pair expansion, including the unused-bond induction and coordinate moment step. The specialized terminal identity is isolated as `ResidualSecondExpansion`.
- `AKLT.Blueprint.Rec.CoveredRatioStatementV2`: still requires deriving the shared local ratio comparison from H1, normally through a common nonnegative local-pattern mixture. The one-point product/summation argument is now proved from this single local comparison.

No counterexample to the frozen target was found. The result is partial because these two proofs are not available; the closed `main` theorem has not been established. A fixed global isometry, first-term kernel comparison, envelope supremum, and U/X removal realization concern neighboring leaves and are not needed for this residual-target reduction.

## ORCH-SUMMARY

- STATUS: PARTIAL for REC080.
- Main module: `AKLT.W.REC080.Main`; it compiles.
- Exact requested closed `AKLT.W.REC080.main` is not delivered.
- Delivered `main_of_dependencies : PairExpansionStatement → CoveredRatioStatementV2 → ResidualTargetBoundStatement`.
- Delivered transparent `ResidualSecondExpansion` and `ResidualCoveredRatio` plus `main_of_residuals`.
- Open leaf: `AKLT.Blueprint.Rec.PairExpansionStatement`.
- Open leaf: `AKLT.Blueprint.Rec.CoveredRatioStatementV2`.
- Both are absent from the supplied proved index.
- Proved closed `terminal_exception_location : TerminalExceptionLocationStatementV2`.
- Proved closed `terminal_exception_count : TerminalExceptionCountStatementV2`.
- Proved the general pointwise comparison conditional only on `CoveredRatioStatementV2`.
- Auxiliary preservation, target degree including legs, fixed-defect invariant, and all tail summation are proved.
- Shared matcher is fully qualified; original stopping set/distance and all original legs are retained.
- Reuses indexed REC011/012/013/039/041/054/096.
- All 78 exported theorems audited; only permitted axioms occur.
- Build: 21.44 s; audit: 4.54 s.
- No files outside REC080 and its report directory were edited.
- Orchestrator should supply the two named leaves or schedule their proofs, then instantiate `main_of_dependencies` to define the exact closed `main`.
