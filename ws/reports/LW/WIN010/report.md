STATUS: PROVED

## Files

- `AKLT/W/WIN010/Main.lean`

## Exported declaration

- `AKLT.W.WIN010.main : AKLT.Blueprint.Win.SeedSeparationStatement`

## Axioms

`#print axioms AKLT.W.WIN010.main`:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.WIN010.Main`
- Result: success; module build 5.6 s, command wall time 13.638 s.

## Proof outline

For any point in `farVolume`, its defining strict inequality and `i ≥ 2`, `shellSpacing u ≥ 2` imply its sup-distance from `y` is greater than 2. Symmetry of `supDist` gives the same bound for the metric used in `setDistance`. `le_iInf` carries the pointwise lower bound 2 to the infimum over the subtype. This also proves the empty case, since the infimum over an empty type is `⊤`.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/WIN010/Main.lean` proving the requested declaration.
- Report: `/home/ubuntu/aklt/reports/LW/WIN010/report.md`.
- Build succeeded with `lake build AKLT.W.WIN010.Main`.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- No residual statements or open issues.
