STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC071/AKLT/W/REC071/Main.lean)

## Exported declaration

`AKLT.W.REC071.main : AKLT.Blueprint.Rec.ShiftedRowsRealStatement`

The proof flattens the `(PairType × ℕ)` ENNReal row into the sum over types and shifts and identifies it with the finite weighted row supplied by `ShiftedWitness`. That row bound proves the flattened ENNReal sum is finite. `ENNReal.summable_toReal` then yields summability of the real row, and `ENNReal.tsum_toReal_eq` converts its total. The pointwise argument uses entry finiteness from `ShiftedWitness`, positivity of the geometric and witness factors, and `mul_ne_top` to establish finiteness of each `shiftKernel` entry before interpreting `realKernel`. The weighted row inequality follows by `toReal_mono` applied to the original ENNReal bound.

## Axioms

Output of `#print axioms AKLT.W.REC071.main`:

```text
'AKLT.W.REC071.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.REC071.Main`
- Result: successful.
- Timing: 12.5 seconds wall time; Lean reported 5.3 seconds for the module.

## Open issues

None.

## ORCH-SUMMARY

- Delivered the closed theorem `AKLT.W.REC071.main` with the requested type.
- Added only `AKLT/W/REC071/Main.lean` in the worktree and this report.
- The module build passed; the theorem uses only `[propext, Classical.choice, Quot.sound]`.
- No residual statements, deviations, or open issues.
