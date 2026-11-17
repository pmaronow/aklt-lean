STATUS: PROVED

## Files

- `AKLT/W/GAP034/Main.lean`
- `/home/ubuntu/aklt/reports/LW/GAP034/report.md`

## Exported declaration

- `AKLT.W.GAP034.main : AKLT.Blueprint.Gap.HaloInjectionStatement`

The proof extracts the coordinate interval bounds from halo-square membership. Each coordinate difference is bounded in absolute value by `2M+2`; the period lower bounds give `2M+2 < L.val` and `2M+2 < N.val`. Equality of residues yields divisibility by the corresponding period, so each integer difference is zero.

## Axioms

Output of `#print axioms AKLT.W.GAP034.main`:

```text
'AKLT.W.GAP034.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.GAP034.Main`
- Result: successful.
- Lean target build time: 3.9 s (the Lake command took about 9.7 s including startup).

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.GAP034.main` with the requested statement in `AKLT/W/GAP034/Main.lean`.
- The requested Lake target builds successfully.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements, limitations, or deviations remain.
