STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_WIN014/AKLT/W/WIN014/Main.lean)
- [report.md](/home/ubuntu/aklt/reports/LW/WIN014/report.md)

## Exported declaration

`AKLT.W.WIN014.main : AKLT.Blueprint.Win.DiagonalEliminationStatement`

The proof forms the finite sum of one-diagonal triangle corrections over the diagonal portion of `c.support`, and sets `d = c + q`. The correction makes every remaining supported edge nearest-neighbor, preserves even degree by additivity of the degree functional, and belongs to `triangleSpan` by construction.

## Axioms

Output of `#print axioms AKLT.W.WIN014.main`:

```text
'AKLT.W.WIN014.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.WIN014.Main`
- Result: success, `AKLT.W.WIN014.Main` built.
- Timing: 8.76 seconds total; Lake reported 3.8 seconds for the module.
- `lake env lean AKLT/W/WIN014/Main.lean` also completed successfully.
- Build emitted non-fatal Lean linter warnings about unused simp arguments and unnecessary sequence focus.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/WIN014/Main.lean` with the requested theorem name and type.
- The diagonal correction is a finite sum indexed by `diagonalSupport c`.
- Exported theorem axioms: `propext`, `Classical.choice`, `Quot.sound`.
- `lake build AKLT.W.WIN014.Main` succeeded (8.76 seconds total).
- Only non-fatal linter warnings remain; no open proof obligations or other deviations.
