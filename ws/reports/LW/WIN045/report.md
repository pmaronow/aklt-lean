STATUS: PROVED

## Files

- `AKLT/W/WIN045/Main.lean`
- `/home/ubuntu/aklt/reports/LW/WIN045/report.md`

## Exported declaration

- `AKLT.W.WIN045.main : AKLT.Blueprint.Win.RawWeightSumStatement`

The proof separates the raw finite sum into near and far sites. For near sites it groups by `radialOffset`, applies the supplied fiber cardinality bound, and compares the finite offset sum to the assumed summable series. For far sites it uses the supplied real depth estimate and bounds the number of sites by the containing square cardinality.

## Axioms

`#print axioms AKLT.W.WIN045.main`:

```text
'AKLT.W.WIN045.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.WIN045.Main`
- Result: success; Lake reported `Built AKLT.W.WIN045.Main (6.4s)`.
- Wall time: 12.64 s (`/usr/bin/time -p`).

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.WIN045.main` with the exact requested type.
- The assigned Lake module builds successfully.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No deviations or open issues.
