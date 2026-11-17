STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_WIN057/AKLT/W/WIN057/Main.lean)

## Exported declaration

`AKLT.W.WIN057.main : AKLT.Blueprint.Win.RemovedPairResponseStatement`

The proof applies `ResponseProperty` to `insert x Y`. It shows the inserted removal is admissible, the two surviving neighbors are retained and distance two, and `x` is their common removed neighbor. For the decay exponent, it proves the boundary depth is bounded by distance to a protected site plus that site's boundary depth, converts the finite `ℕ∞` depth to `ℕ`, and only then uses subtraction by three.

## Axioms

`#print axioms AKLT.W.WIN057.main`:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.WIN057.Main`
- Result: successful; Lake replayed the compiled module, with 12.4 seconds wall time for the command.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/WIN057/Main.lean` with the requested theorem and exact type.
- Status: PROVED; the requested Lake build succeeded.
- `#print axioms`: `[propext, Classical.choice, Quot.sound]`.
- No existing project files were edited; no helper declarations remain as assumptions.
- Open issues: none.
