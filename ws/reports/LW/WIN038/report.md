STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_WIN038/AKLT/W/WIN038/Main.lean`
- `/home/ubuntu/aklt/reports/LW/WIN038/report.md`

## Exported declaration

- `AKLT.W.WIN038.main : AKLT.Blueprint.Win.RawDistanceObstructionsStatement`

The proof establishes the pointwise distance bound for every `x` and every site outside `cutVolume`; therefore the hypotheses `CutSetup` and `x ∈ cutRaw` are not needed. The argument splits the complement into window sites, sites outside the square, and square sites outside `farVolume`, then converts pointwise natural-distance bounds through `Nat.ceil` and the finite `ℕ∞` boundary depth.

## Axioms

`#print axioms AKLT.W.WIN038.main`:

```text
'AKLT.W.WIN038.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the allowed axioms.

## Build

- `lake build AKLT.W.WIN038.Main` — succeeded; module build reported 4.0 s, total command wall time 11.39 s.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/WIN038/Main.lean` with `AKLT.W.WIN038.main` at the requested type.
- The requested Lake build succeeds.
- The theorem uses only allowed axioms: `propext`, `Classical.choice`, `Quot.sound`.
- The geometric inequality is proved for arbitrary `x`; `CutSetup` and raw-boundary membership are unused.
- No open proof obligations or deviations remain.
