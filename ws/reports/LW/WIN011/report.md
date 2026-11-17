STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_WIN011/AKLT/W/WIN011/Main.lean)
- This report: `/home/ubuntu/aklt/reports/LW/WIN011/report.md`

## Exported declaration

- `AKLT.W.WIN011.main : AKLT.Blueprint.Win.FiniteDepthStatement`

The proof chooses an exterior point using a maximum first coordinate of the
finite set. The exterior subtype is therefore nonempty, so `ENat.exists_eq_iInf`
provides a point attaining the distance infimum. The attained natural distance
proves finiteness and the `toNat` identity. Distance zero is equivalent to the
point itself being exterior. The final bound follows from the triangle
inequality for `latticeDist` and attainment at the second point.

## Axioms

`#print axioms main` output:

```text
'AKLT.W.WIN011.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No forbidden proof escape hatches are used.

## Build

- Command: `time lake build AKLT.W.WIN011.Main`
- Result: successful; module built in 4.4 s, command elapsed 9.318 s.
- The compiler emitted only style warnings for the local `Nonempty` instance and
  two `congr`/`omega` sequences.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/WIN011/Main.lean` with the exact requested theorem name and type.
- `lake build AKLT.W.WIN011.Main` succeeds.
- `main` uses only allowed axioms: propext, Classical.choice, Quot.sound.
- No residual statements, deviations, or open issues.
