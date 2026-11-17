STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC010/AKLT/W/REC010/Main.lean)
- This report: `/home/ubuntu/aklt/reports/LW/REC010/report.md`

## Exported declarations

- `AKLT.W.REC010.ResidualOriginalNormalizerPositive : Prop` — for every `Departure` and pin choice, its original partition normalizer is strictly positive.
- `AKLT.W.REC010.ResidualTraceNormalizerPositive : Prop` — for every `Departure` and pin choice, its one-step traced partition normalizer is strictly positive.
- `AKLT.W.REC010.traceStep_auxiliary` — an admissible one-step trace of an auxiliary network remains auxiliary.
- `AKLT.W.REC010.main (hOriginal) (hTrace) : AKLT.Blueprint.Rec.StepRatioPositiveStatement` — derives the requested ratio positivity from the two explicit normalizer residuals.

The requested closed declaration `AKLT.W.REC010.main : AKLT.Blueprint.Rec.StepRatioPositiveStatement` is not yet proved: the delivered `main` has the two residual normalizer assumptions. The ratio calculation itself is complete, and the trace-validity argument compiles.

## Axioms

`#print axioms` output:

```text
'AKLT.W.REC010.traceStep_auxiliary' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC010.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the permitted axioms. No `sorry`, `admit`, or other forbidden escape is used.

## Build

- Command: `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.REC010.Main`
- Result: successful; final run wall time 9.6 s, Lean module compilation 4.6 s.
- The compiler reports a non-fatal simp linter warning at `Main.lean:46`.

## Open issues

The two exact remaining obligations are `ResidualOriginalNormalizerPositive` and `ResidualTraceNormalizerPositive`. They require proving strict positivity of the network partition sums from the finite spin weights, degree-four local factor bounds, and a positive assignment avoiding zero bond and pin factors. The trace-preservation lemma is available to transport any general auxiliary-network positivity result to this traced network, but that positivity result is not proved here.

## ORCH-SUMMARY

- Delivered a compiled conditional ratio proof and a proof that `traceStep` preserves `Auxiliary` validity.
- `AKLT.W.REC010.main` currently takes `ResidualOriginalNormalizerPositive` and `ResidualTraceNormalizerPositive`; it does not have the requested closed type.
- Open residuals: `AKLT.W.REC010.ResidualOriginalNormalizerPositive`, `AKLT.W.REC010.ResidualTraceNormalizerPositive`.
- Both residuals are strict partition-normalizer positivity statements, one for the original departure and one for its trace.
- Build passed with `lake build AKLT.W.REC010.Main`; only permitted axioms appear.
- Orchestrator should treat this as PARTIAL and either prove the two normalizer residuals or assign their finite-network positivity proof.
