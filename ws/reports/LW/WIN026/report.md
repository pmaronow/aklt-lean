STATUS: PROVED

## Delivered files

- `AKLT/W/WIN026/Main.lean`
- `/home/ubuntu/aklt/reports/LW/WIN026/report.md`

## Exported declaration

`AKLT.W.WIN026.main : AKLT.Blueprint.Win.CrossOverlapStatement`

The proof extracts coordinate differences bounded by one from `supDist x y = 1`. If one coordinate agrees, the center `x` lies in both crosses. If both coordinates differ, `(x.1, y.2)` is a common axial neighbor.

## Axioms

`#print axioms AKLT.W.WIN026.main`:

```text
'AKLT.W.WIN026.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.WIN026.Main` — completed successfully in 9.23 s (module build reported 4.4 s).

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.WIN026.main` with the requested statement and exact name.
- The module builds successfully.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements, limitations, or deviations.
- No orchestrator decision is needed.
