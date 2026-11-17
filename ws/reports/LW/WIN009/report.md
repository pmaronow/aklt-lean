STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_WIN009/AKLT/W/WIN009/Main.lean`
- `/home/ubuntu/aklt/reports/LW/WIN009/report.md`

## Exported declaration

`AKLT.W.WIN009.main : AKLT.Blueprint.Win.PredecessorShellStatement`

The proof extracts a point of `farVolume` at sup-distance at most one from the given point. It establishes the sup-distance triangle inequality from the coordinate definition, then uses integrality and the real floor bounds to identify the point's radius with `floor ((i - 1) * shellSpacing u)`. The empty-set case is excluded because its infimum distance is `⊤`.

## Axioms

Output of `#print axioms AKLT.W.WIN009.main`:

```text
'AKLT.W.WIN009.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.WIN009.Main` — succeeded; target module built in 4.7 s (Lake reported 8955/8955 jobs).
- `lake env lean /tmp/win009_check.lean` — confirmed the exact declaration type and printed the axioms above.

## Open issues

None.

## ORCH-SUMMARY

- Delivered the requested theorem at the exact name and type in `AKLT/W/WIN009/Main.lean`.
- The requested module build succeeded.
- The theorem uses only the allowed axioms: `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements, deviations, or open issues.
