STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_WIN003/AKLT/W/WIN003/Main.lean`
- `/home/ubuntu/aklt/reports/LW/WIN003/report.md`

## Exported declaration

`AKLT.W.WIN003.main : AKLT.Blueprint.Win.ExceptionalLocalizationStatement`

For each exceptional index, the proof unpacks its shell point and nearby square corner. The index bound gives `shellRadius u i ≤ s²+s`, where `s = shellSpacing u`. Sup-distance triangle inequalities then show the corner is within `s²+4s/3 < u` of `y`; applying the triangle inequality in both directions bounds the radial error by the witness distance, which is strictly below `s/3`.

## Axioms

`#print axioms AKLT.W.WIN003.main`:

```text
'AKLT.W.WIN003.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.WIN003.Main`
- Result: successful; Lake reported the module build at 6.6 s (12.5 s total command wall time).
- Axiom check: `lake env lean /tmp/PrintWIN003.lean`, successful.

## Open issues

None.

## ORCH-SUMMARY

- Delivered the requested theorem `AKLT.W.WIN003.main` in `AKLT/W/WIN003/Main.lean`.
- The theorem has the exact requested statement and compiles with `lake build AKLT.W.WIN003.Main`.
- Axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
- No frozen statement or existing project file was changed.
- No open issues or deviations.
