STATUS: PROVED

## Files

- `AKLT/W/WIN037/Main.lean`

## Exported declaration

`AKLT.W.WIN037.main : AKLT.Blueprint.Win.RawRangeStatement`

## Axioms

`#print axioms AKLT.W.WIN037.main` reports:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.WIN037.Main`
- Result: successful
- Timing: 10.7 s total; Lean module compilation 4.9 s

## Proof outline

A raw-boundary site has a star neighbour in the taper. Coordinate bounds from `starBall` give a one-step bound on `supDist`, which yields one-step bounds on radial offset and square depth. These prove the radial upper bound and near-case lower height bound. The lower height is positive, so the site lies in the square; its failure to belong to the taper then forces the strict upper height bound.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/WIN037/Main.lean` and proved `AKLT.W.WIN037.main` with the requested type.
- Build succeeded with `lake build AKLT.W.WIN037.Main`.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements, deviations, or open issues.
