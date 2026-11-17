STATUS: PROVED

## Files

- `AKLT/W/H3M012/Main.lean`

## Exported declaration

- `AKLT.W.H3M012.main : AKLT.Blueprint.H3.DepartureBalanceStatement`

The proof reduces the departure and arrival counts to filtered ranges. Positive-index departures inject into arrivals under the index shift `j ↦ j - 1`; index zero contributes at most one. The argument does not use a trail premise.

## Axioms

`#print axioms AKLT.W.H3M012.main`:

```text
'AKLT.W.H3M012.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.H3M012.Main`
- Result: successful
- Lean target time: 5.5 s

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.H3M012.main` with the exact requested name and type.
- The finite counting proof requires no trail hypothesis.
- Build succeeded; reported axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
- No open issues or deviations.
