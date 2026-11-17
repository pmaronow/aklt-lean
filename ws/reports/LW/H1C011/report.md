STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1C011/AKLT/W/H1C011/Main.lean)
- [report.md](/home/ubuntu/aklt/reports/LW/H1C011/report.md)

## Exported declaration

`AKLT.W.H1C011.main : AKLT.Cert.H1.Production.Leaves.acceptedLookup`

The proof inducts on the bundle list and projects the acceptance proof for each member. The recursive step returns the full `Bundle.Accepted` proposition. This preserves all its components: layout checks (basis, sector network, remapping, and lengths), sector row acceptance, the block checker, and the separate lower-triangularity check.

## Axioms

`#print axioms AKLT.W.H1C011.main`:

```text
'AKLT.W.H1C011.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

`lake build AKLT.W.H1C011.Main` — succeeded; target compilation reported 3.9 s (8.9 s wall time for the command).

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/H1C011/Main.lean` with the requested theorem name and type.
- Proved by list induction, returning each complete bundle acceptance record.
- Layout, row, checker/Gram, and triangularity obligations are retained.
- Build succeeded; allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements or known open issues.
