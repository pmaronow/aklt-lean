STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_WIN041/AKLT/W/WIN041/Main.lean)
- `/home/ubuntu/aklt/reports/LW/WIN041/report.md`

## Exported declaration

`AKLT.W.WIN041.main : AKLT.Blueprint.Win.SignedSideExclusionStatement`

The proof derives the scale bounds from `CutSetup`, then compares the signed depth of a shell side with the height `h`. If the original line is on the selected exterior side, its shifted depth is at most `j`; if it is beyond the opposite side, its shifted depth exceeds `32+j`. For an internal line, a shell point inside the square supplies the `ParallelClearance` hypothesis, giving shifted depth greater than `32+j`. Each case contradicts `30+j ≤ h < 32+j` or the assumed coincidence.

## Axioms

`#print axioms AKLT.W.WIN041.main`:

```text
'AKLT.W.WIN041.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.WIN041.Main` — succeeded; final target build reported 7.7 seconds.
- `lake env lean /tmp/win041_axioms.lean` — succeeded; confirmed the theorem type and axioms.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.WIN041.main` with the exact requested statement.
- The target module builds successfully.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound` only.
- No residual statements or deviations remain.
