STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_REC030/AKLT/W/REC030/Main.lean`
- `/home/ubuntu/aklt/reports/LW/REC030/report.md`

## Exported declaration

`AKLT.W.REC030.main : AKLT.Blueprint.Rec.BallSlotConvexityStatement`

The proof takes (t=(1+\sqrt{\mathrm{normSq}(b)})/2) and the normalized direction (e=b/\sqrt{\mathrm{normSq}(b)}) when (b\ne0). When (b=0), it uses a coordinate unit vector. It proves the unit norm, weight bounds, and pointwise affine identity directly from the finite-coordinate dot product.

## Axioms

`#print axioms AKLT.W.REC030.main`:

```text
'AKLT.W.REC030.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.REC030.Main` — successful; module compile reported 5.5 s.
- Axiom audit via `lake env lean --stdin` — successful; reported only the allowed axioms above.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.REC030.main` with the exact requested type.
- The target is proved directly, including the zero-vector case.
- `lake build AKLT.W.REC030.Main` succeeds.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements or deviations remain.
