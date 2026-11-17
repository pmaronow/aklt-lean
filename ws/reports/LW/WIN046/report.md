STATUS: PROVED

## Files

- `AKLT/W/WIN046/Main.lean`

## Exported declaration

- `AKLT.W.WIN046.main : AKLT.Blueprint.Win.ThickDepthStatement`

The proof unfolds `boundaryDepth` as an infimum over exterior sites. It establishes the lattice-distance triangle inequality and that each point in a cross is at distance at most one from its centre. Thus every exterior site is at distance at least 13 from any point of a cross whose centre has depth at least 14. This gives both membership in `G` and depth at least 13 for the entire thickening.

## Axioms

`#print axioms AKLT.W.WIN046.main`:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.WIN046.Main`
- Result: successful
- Module build time: 4.4 s (Lean reported)

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/WIN046/Main.lean` with `AKLT.W.WIN046.main` proving `AKLT.Blueprint.Win.ThickDepthStatement`.
- Build succeeded with `lake build AKLT.W.WIN046.Main`.
- Axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
- No helpers outside the assigned directory and no existing files were changed.
- No open issues or deviations.
