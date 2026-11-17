STATUS: PROVED

## Files

- `AKLT/W/REC036/Main.lean`
- `/home/ubuntu/aklt/reports/LW/REC036/report.md`

## Exported declaration

- `AKLT.W.REC036.main : AKLT.Blueprint.Rec.AlphaAnalyticStatement`

The proof represents the reciprocal logarithmic mean as the integral of an affine reciprocal. It lowers the first argument using monotonicity of the reciprocal mean, retains the negative (J)-term, proves the resulting two-term kernel antitone in both (J) arguments, and applies the bounds (J_t \ge 116/125), (J_0 \ge 1).

## Axioms

Output of `#print axioms AKLT.W.REC036.main`:

```text
'AKLT.W.REC036.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.REC036.Main`
- Result: successful; Lean reported the target built in 8.2 seconds.
- Axiom audit command: `lake env lean /tmp/rec036_axioms.lean` (6.3 seconds including startup), where the file imports `AKLT.W.REC036.Main` and prints the theorem axioms.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/REC036/Main.lean` with the exact theorem `AKLT.W.REC036.main : AKLT.Blueprint.Rec.AlphaAnalyticStatement`.
- Proved the reciprocal logarithmic mean integral identity and the needed monotonicity lemmas as private helpers.
- Preserved the subtraction term while lowering (I_t), then applied the common kernel monotonicity to both (J) arguments.
- Build: `lake build AKLT.W.REC036.Main` succeeded (8.2 seconds for target).
- Axioms: `[propext, Classical.choice, Quot.sound]`.
- Open issues: none; no deviations.
