STATUS: PROVED

## Delivered files

- `/home/ubuntu/aklt/wt/LW_H3M029/AKLT/W/H3M029/Main.lean`
- `/home/ubuntu/aklt/reports/LW/H3M029/report.md`

## Exported declaration

`AKLT.W.H3M029.main : AKLT.Blueprint.H3.KernelSeriesRegroupingStatement`

The proof specializes the shifted kernel at `theta = 1`, moves the witness factor through the ENNReal sums, commutes the length and shift sums with the finite type sum, removes shifts outside `lengthShifts` using the supplied zero-support premise, and converts the resulting finite nonnegative rational partition to `ENNReal.ofReal` before applying the supplied row equality.

## Axioms

`#print axioms AKLT.W.H3M029.main`:

```text
'AKLT.W.H3M029.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the permitted axioms.

## Build

Command: `lake build AKLT.W.H3M029.Main`

Result: successful. Lake reported the module build at 5.0 seconds; measured command elapsed time was 12.82 seconds including Lake startup and build orchestration.

## Open issues

None.

## ORCH-SUMMARY

- Delivered the requested theorem in `AKLT/W/H3M029/Main.lean` with the exact name and type.
- The theorem compiles with `lake build AKLT.W.H3M029.Main`.
- `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements, deviations, or open issues.
