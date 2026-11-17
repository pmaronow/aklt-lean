STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_Q010/AKLT/W/Q010/Main.lean)
- [report.md](/home/ubuntu/aklt/reports/LW/Q010/report.md)

## Exported declaration

`AKLT.W.Q010.main : AKLT.Blueprint.Q.QuarticKernelEvaluationStatement`

The proof extracts the diagonal and `(1,0)` density entries, pairs powers for `j ≤ k`, and uses the `(0,1)` entry for `j > k`. The three factors contribute powers of `1/2` whose exponents sum to four, yielding the kernel normalization `1/16`.

## Axioms

`#print axioms AKLT.W.Q010.main`:

```text
'AKLT.W.Q010.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the permitted Lean axioms.

## Build

- `lake build AKLT.W.Q010.Main` — succeeded; final run took 13.1 seconds wall time (7.4 seconds reported for the module build).
- `lake env lean /tmp/Q010Axioms.lean` — succeeded and printed the axiom list above.

The build emits deprecation warnings for `if_pos` and `if_neg`; they do not affect the result.

## Open issues

No proof gaps or mathematical issues remain.

## ORCH-SUMMARY

- Delivered `AKLT/W/Q010/Main.lean` with the exact requested theorem and type.
- Status is `PROVED`.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- Final requested Lake build succeeded.
- Compiler reports only the `if_pos` and `if_neg` deprecation warnings.
- No residual statements or orchestration decisions are needed.
