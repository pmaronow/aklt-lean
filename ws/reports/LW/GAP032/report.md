STATUS: PROVED

## Files

- `AKLT/W/GAP032/Main.lean`

## Exported declaration

- `AKLT.W.GAP032.main : AKLT.Blueprint.Gap.TorusColourStatement`

The proof verifies neighboring residues of `cycleColour` for every period of at least three, including the wrap edge and the odd-cycle last-site branch, then applies this in each torus direction.

## Axioms

`#print axioms AKLT.W.GAP032.main`:

```text
depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.GAP032.Main`
- Result: succeeded; module compilation reported 3.7 s, command elapsed 8.39 s.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.GAP032.main` with the required type in `AKLT/W/GAP032/Main.lean`.
- Proof covers both coordinate directions, odd/even cycle formulas, and period-three wrap edges.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- `lake build AKLT.W.GAP032.Main` succeeded (8.39 s command elapsed).
- No deviations or open issues.
