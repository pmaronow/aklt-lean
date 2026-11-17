STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_GAP049/AKLT/W/GAP049/Main.lean)
- This report: `/home/ubuntu/aklt/reports/LW/GAP049/report.md`

## Exported declaration

`AKLT.W.GAP049.main : AKLT.Blueprint.Gap.FiniteTrialFailureStatement`

The theorem proves that for a finite chain with probability initial weight and normalized transition kernels, if every selected trial has conditional event mass at least `δ`, then the mass of paths failing all selected events is at most `(1 - δ)^J.card`. The proof orders trials by their `Fin` index and inducts by conditioning on the last transition. It includes `δ = 0`, `δ = 1`, and the empty trial set; no independence assumption is used.

## Axioms

`#print axioms AKLT.W.GAP049.main`:

```text
[propext, Classical.choice, Quot.sound]
```

These are the permitted classical and quotient axioms. No residual propositions are used.

## Build

Command: `time lake build AKLT.W.GAP049.Main`

Result: succeeded. Lake reported 6.2 seconds for the target; command wall time was 11.038 seconds. The build emitted style/deprecation warnings only.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/GAP049/Main.lean` with the requested theorem name and type.
- The finite induction uses the complete preceding path to condition each next trial.
- Empty `J` and endpoint values `δ = 0, 1` are included.
- No independence assumption is needed; no residual theorem remains.
- Build succeeded; `main` depends only on `[propext, Classical.choice, Quot.sound]`.
- No deviations or open issues.
