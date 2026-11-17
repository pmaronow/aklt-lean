STATUS: PROVED

## Files

- `AKLT/W/WIN016/Main.lean`
- `/home/ubuntu/aklt/reports/LW/WIN016/report.md`

## Exported declaration

`AKLT.W.WIN016.main : AKLT.Blueprint.Win.TailSupportStatement`

The proof takes `P = Finset.Icc (-R) R ×ˢ Finset.Icc (-R) R`. If the first coordinate is outside the interval, `ChainInBox` forces every horizontal coefficient in that column to vanish. If the second coordinate is above the interval, the tail is empty; if below, every summand is included and the assumed zero column flux applies.

## Axioms

`#print axioms main`:

```text
'AKLT.W.WIN016.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.WIN016.Main`
- Result: successful (`Built AKLT.W.WIN016.Main`)
- Timing: 9.7 s wall time for the command; Lean module reported 4.7 s.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/WIN016/Main.lean` with `AKLT.W.WIN016.main` proving the requested frozen statement.
- Witness: the finite coordinate square `[-R,R] × [-R,R]`.
- Build succeeded with `lake build AKLT.W.WIN016.Main`.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- No residual statements, limitations, or deviations.
