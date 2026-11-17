STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_WIN021/AKLT/W/WIN021/Main.lean`
- `/home/ubuntu/aklt/reports/LW/WIN021/report.md`

## Exported declaration

`AKLT.W.WIN021.main : AKLT.Blueprint.Win.TriangleCutParityStatement`

The proof expands triangle parity into the three edge indicators. It shows that a triangle edge lies in `cutEdges A` exactly when its endpoints have different membership in `A`. Equal-side edges cannot lie in `E`; among the two crossing edges, `LinkClosed` makes membership in `E` equivalent, so their indicators cancel in `ZMod 2`.

## Axioms

`#print axioms main`:

```text
'AKLT.W.WIN021.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.WIN021.Main`
- Result: successful.
- Final successful invocation: 11.7 seconds wall time; Lean module build reported 6.8 seconds.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/WIN021/Main.lean` proving the requested closed statement.
- Exported declaration: `AKLT.W.WIN021.main : AKLT.Blueprint.Win.TriangleCutParityStatement`.
- Build passed with `lake build AKLT.W.WIN021.Main`.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No limitations or deviations; no open issues.
