STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_WIN043/AKLT/W/WIN043/Main.lean`

## Exported declaration

`AKLT.W.WIN043.main : AKLT.Blueprint.Win.RawLayerCountStatement`

The proof covers each filtered layer by four candidate square-boundary intersections: two radii about `y` and two integer depth levels. The half-open interval `[30+j, 32+j)` has exactly two integer values. Each intersection has cardinality at most eight by the supplied square-intersection hypothesis when both radii are positive; zero or negative radii are handled directly. Thus the cover has cardinality at most `2 × 2 × 8 = 32`, which implies the required bound of 48.

## Axioms

`#print axioms AKLT.W.WIN043.main` reports:

```text
'AKLT.W.WIN043.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.WIN043.Main` — succeeded (Lake reported 12s for the final successful build).
- The theorem was also checked with `lake env lean /tmp/win043_axioms.lean`.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/WIN043/Main.lean` with the exact requested theorem name and type.
- `lake build AKLT.W.WIN043.Main` succeeds.
- `#print axioms` lists only `propext`, `Classical.choice`, and `Quot.sound`.
- The proof uses a four-intersection cover and proves the stronger bound 32.
- No residual statements or open issues remain.
