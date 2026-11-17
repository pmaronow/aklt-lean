STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_WIN007/AKLT/W/WIN007/Main.lean`

## Exported declaration

- `AKLT.W.WIN007.main : AKLT.Blueprint.Win.NearShellCountStatement`

## Proof summary

From the exterior-distance infimum, extract an exterior lattice point within distance `l`; this places the shell point in one of four width-`l` strips along the square boundary. A shell point lies on one of the four coordinate sides of its sup-distance square. `ParallelClearance` and the threshold inequality `l < shellSpacing u / 3` exclude a side parallel to the boundary strip. The remaining eight side/strip intersections each inject into an integer interval of cardinality `l`. Their union therefore has cardinality at most `8*l`.

## Axioms

`#print axioms AKLT.W.WIN007.main`:

```text
[propext, Classical.choice, Quot.sound]
```

All are allowed axioms.

## Build

- `lake build AKLT.W.WIN007.Main` — successful; Lean module build reported 7.9 s (17.3 s wall time for the Lake invocation).

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.WIN007.main` with the exact requested type in `AKLT/W/WIN007/Main.lean`.
- The proof uses eight shell-side/boundary-strip intersections, each of size at most `l`.
- Build passed with `lake build AKLT.W.WIN007.Main`.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- No deviations or open issues.
