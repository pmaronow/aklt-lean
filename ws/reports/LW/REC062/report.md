STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_REC062/AKLT/W/REC062/Main.lean`
- `/home/ubuntu/aklt/reports/LW/REC062/report.md`

## Exported declaration

- `AKLT.W.REC062.main : AKLT.Blueprint.Rec.ShiftGeometryStatement`

The proof bounds the lattice distance along every interval of the direction word by its length. It shows every site in a response pair is a neighbour of its departure, bounds its distances to the two endpoints by `i + 1` and `n - i + 1`, and uses the smaller bound to establish the natural-number supremum estimate. Casting that estimate to `ℝ` proves the requested `n / 2 + 1` bound.

## Axioms

`#print axioms AKLT.W.REC062.main`:

```text
'AKLT.W.REC062.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.REC062.Main`
- Result: successful
- Timing: 16.8 seconds wall time for the reported timed invocation; Lean reported 6.0 seconds for the module build.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.REC062.main` with the exact requested statement.
- Compiles with `lake build AKLT.W.REC062.Main`.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements, deviations, or open issues.
