STATUS: PROVED

## Files

- `AKLT/W/WIN039/Main.lean`
- `/home/ubuntu/aklt/reports/LW/WIN039/report.md`

## Exported declaration

- `AKLT.W.WIN039.main : AKLT.Blueprint.Win.RawDepthArithmeticStatement`

The proof lower-bounds each of the three entries in the nested minimum. The general lower bound uses the near/far split; the near case additionally bounds `max t 16 - 2`, and the far case bounds `s / 12 - 1`.

## Axioms

`#print axioms AKLT.W.WIN039.main`:

```text
'AKLT.W.WIN039.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.WIN039.Main` — passed; Lake reported 6.2s for the module build.
- Axioms were checked with `lake env lean /tmp/WIN039Axioms.lean`.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.WIN039.main` with the requested exact name and type.
- Proof uses only the statement's hypotheses and elementary real arithmetic.
- Build passed; axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No open issues or deviations.
