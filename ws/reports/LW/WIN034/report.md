STATUS: PROVED

## Files

- `AKLT/W/WIN034/Main.lean`
- `/home/ubuntu/aklt/reports/LW/WIN034/report.md`

## Exported declaration

- `AKLT.W.WIN034.main : AKLT.Blueprint.Win.SquareExteriorStatement`

The proof constructs nearest-neighbour coordinate walks. Exterior sites connect to the row immediately above the square while remaining outside it; points on that row connect horizontally. The proof uses only the definitions of the square, adjacency, `JoinedIn`, and `ConnectedIn`, plus Mathlib.

## Axiom audit

`#print axioms AKLT.W.WIN034.main`:

```text
'AKLT.W.WIN034.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.WIN034.Main` — succeeded; Lean reported 4.4 s for the module.
- `lake env lean /tmp/WIN034_audit.lean` — succeeded; confirmed the exact type and printed the axiom list above (6.6 s).

## Open issues

None.

## ORCH-SUMMARY

- Proved `AKLT.W.WIN034.main : AKLT.Blueprint.Win.SquareExteriorStatement` in `AKLT/W/WIN034/Main.lean`.
- The proof uses explicit lattice coordinate paths outside the square and along its top exterior row.
- Build succeeded with `lake build AKLT.W.WIN034.Main` (4.4 s).
- Axiom dependencies are `[propext, Classical.choice, Quot.sound]`.
- No residual statements, limitations, or deviations remain.
