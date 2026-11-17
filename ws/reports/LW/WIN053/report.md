STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_WIN053/AKLT/W/WIN053/Main.lean)

## Exported declaration

`AKLT.W.WIN053.main : AKLT.Blueprint.Win.NeighbourFibresStatement`

The proof establishes the nonadjacency and degree bounds for the survivor sites, factors the conditional weight on each fibre into one-site weights, and applies `ThreeFactorMeanStatement` to the resulting local means. It proves the pair identity by factoring the two-site conditional moment coordinatewise.

## Axioms

Output of `#print axioms AKLT.W.WIN053.main`:

```text
'AKLT.W.WIN053.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.WIN053.Main`
- Result: successful; Lake reports the module built in 7.8 seconds (13.7 seconds wall time for the command).
- The build reports Lean linter and deprecation warnings in `Main.lean`; there are no errors.

## Open issues

None.

## ORCH-SUMMARY

- Delivered the requested theorem in `AKLT/W/WIN053/Main.lean`.
- The theorem has exactly the requested name and type.
- The requested Lake build succeeds.
- `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements or deviations remain.
