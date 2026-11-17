STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC026/AKLT/W/REC026/Main.lean)

## Exported declaration

`AKLT.W.REC026.main : AKLT.Blueprint.Rec.EightTermRemainderStatement`

The proof gets the lower remainder bound from Mathlib's finite logarithm series lemma. For the sharper upper bound, it compares the remainder with `t^17 / (17 * (1 - t^2))` on `[0,t]`: the comparison function has nonnegative derivative, and its value at zero is zero.

## Axioms

`#print axioms AKLT.W.REC026.main`:

```text
'AKLT.W.REC026.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.REC026.Main` — succeeded; module compilation reported 8.1s (15.0s wall time for the command).
- Axiom check with `lake env lean /tmp/REC026Axioms.lean` — succeeded; 4.7s.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/REC026/Main.lean` with `AKLT.W.REC026.main` proving the requested closed statement.
- The file compiles with the requested Lake build command.
- Exported theorem axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
- No helper files, residual statements, or deviations; no open issues.
