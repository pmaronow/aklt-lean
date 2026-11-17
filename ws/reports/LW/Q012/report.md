STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_Q012/AKLT/W/Q012/Main.lean)

## Exported declaration

`AKLT.W.Q012.main : AKLT.Blueprint.Q.QuarticOffDiagonalStatement`

The proof unfolds the finite complex moment and quartic kernel, enumerates the coordinate families and independent signs of the twelve labels, and simplifies the resulting finite sums. Sign-paired terms cancel; the remaining quartic cases use the golden-ratio identity `goldenRatio ^ 4 = 3 * goldenRatio ^ 2 - 1`. The `j = k` cases close from the explicit `j ≠ k` hypothesis.

## Axioms

`#print axioms AKLT.W.Q012.main`:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

`lake build AKLT.W.Q012.Main` succeeded. Lake reported the module built in 67 seconds (72.02 seconds elapsed including command overhead).

## Open issues

None.

## ORCH-SUMMARY

- Proved `AKLT.W.Q012.main` with the exact requested type.
- Delivered `AKLT/W/Q012/Main.lean` and this report.
- Checked axioms: `propext`, `Classical.choice`, `Quot.sound`.
- `lake build AKLT.W.Q012.Main` succeeded.
- No residual statements, deviations, or open issues.
