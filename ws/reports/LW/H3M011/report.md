STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_H3M011/AKLT/W/H3M011/Main.lean`

## Exported declaration

`AKLT.W.H3M011.main : AKLT.Blueprint.H3.IncidentBondBudgetStatement`

The proof forms a disjoint sum of departure and arrival occurrences at the chosen site. It maps each occurrence to the Compass direction pointing from that site along its used bond. Distinct-bond injectivity rules out duplicate bonds, and the nonzero Compass steps rule out counting one bond once as an arrival and once as a departure. Thus the occurrence set injects into the four Compass directions.

## Axioms

`#print axioms AKLT.W.H3M011.main`:

```text
'AKLT.W.H3M011.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `export PATH="$HOME/.elan/bin:$PATH"; lake build AKLT.W.H3M011.Main`
- Result: successful.
- Lean module build time: 6.7 s; command wall time: 13.1 s.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.H3M011.main` with the exact requested type in `AKLT/W/H3M011/Main.lean`.
- Proved the arrival/departure incident-bond count bound from `IsTrail` bond injectivity and Compass's four directions.
- Build succeeded with `lake build AKLT.W.H3M011.Main`.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No deviations or open proof obligations.
