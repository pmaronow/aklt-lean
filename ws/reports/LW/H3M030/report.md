STATUS: PROVED

## Files

- `AKLT/W/H3M030/Main.lean`

## Exported declaration

- `AKLT.W.H3M030.main : AKLT.Blueprint.H3.CutoffSeriesLiftStatement`

The proof establishes nonnegativity of `B` from the zero cutoff, expresses the ENNReal tsum as the supremum of its range partial sums, erases the zero index, bounds the remaining indices by `Icc 1 N`, and applies monotonicity of `ENNReal.ofReal`.

## Axioms

`#print axioms AKLT.W.H3M030.main`:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.H3M030.Main`
- Result: successful; final incremental module build reported 6.8s.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.H3M030.main` with the exact requested statement.
- New Lean file: `AKLT/W/H3M030/Main.lean`; report: `/home/ubuntu/aklt/reports/LW/H3M030/report.md`.
- Build command `lake build AKLT.W.H3M030.Main` succeeded.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- No open issues or deviations.
