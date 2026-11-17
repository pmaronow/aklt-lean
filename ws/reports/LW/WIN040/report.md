STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_WIN040/AKLT/W/WIN040/Main.lean`

## Exported declaration

- `AKLT.W.WIN040.main : AKLT.Blueprint.Win.RawHeightStatement`

The proof expands `cutRaw` as the raw boundary of the taper and chooses its taper neighbour. The star-ball condition bounds the sup-distance step by one. Separate lemmas transfer the one-step bound to `radialOffset` and `squareDepth`; combining these with the taper's depth condition gives `30 + radialOffset(x) ≤ squareDepth(x)` without a near-range premise.

## Axiom audit

`#print axioms AKLT.W.WIN040.main`:

```text
'AKLT.W.WIN040.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.WIN040.Main`
- Result: successful
- Timing: target module 4.1 s; command wall time 9.4 s

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/WIN040/Main.lean` with `AKLT.W.WIN040.main` proving the requested statement.
- Build succeeded with `lake build AKLT.W.WIN040.Main`.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements, deviations, or open issues.
