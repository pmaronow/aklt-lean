STATUS: PROVED

## Files

- `AKLT/W/GAP039/Main.lean`
- `/home/ubuntu/aklt/reports/LW/GAP039/report.md`

## Exported declaration

`AKLT.W.GAP039.main : AKLT.Blueprint.Gap.SquareInternalEdgesStatement`

The proof decomposes the oriented-once internal edge set into horizontal and vertical image finsets. Integer interval cardinalities give `2M` starting positions and `2M+1` rows or columns; the two edge orientations are disjoint. The signed integer intervals handle `M = 0` directly, with the start interval empty and no natural-number subtraction in the edge count.

## Axioms

Output of `#print axioms AKLT.W.GAP039.main`:

```text
'AKLT.W.GAP039.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

Command: `lake build AKLT.W.GAP039.Main`

Result: successful; Lake reported the module built in 6.0 seconds, with 16.42 seconds total wall time.

A separate `lake env lean /tmp/GAP039Axioms.lean` invocation checked the theorem type and axioms; it completed in 7.50 seconds.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.GAP039.main` with the required type in `AKLT/W/GAP039/Main.lean`.
- Lake build succeeded.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- The count includes `M = 0`; no unsigned subtraction is used for the edge count.
- No open declarations or limitations.
