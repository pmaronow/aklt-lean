STATUS: PROVED

## Files

- `AKLT/W/H1M011/Main.lean`
- `/home/ubuntu/aklt/reports/LW/H1M011/report.md`

## Exported declaration

`AKLT.W.H1M011.main : AKLT.Blueprint.H1.OriginalRawEvaluationStatement`

The proof identifies `supportSpins π.active` with `π.spins`, evaluates the formal-dot products through the polynomial evaluation ring hom, and matches the resulting bond and pin factors termwise in the finite spin sum. The final Boolean split selects `patternCurrent` or `patternNext`.

## Axioms

`#print axioms AKLT.W.H1M011.main`:

```text
'AKLT.W.H1M011.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the allowed axioms.

## Build

Command: `lake build AKLT.W.H1M011.Main`

Result: successful; Lean target build reported 3.8 s (command wall time 9.4 s).

A separate `lake env lean --stdin` check of the declaration and its axioms completed in 3.8 s.

## Open issues

None.

## ORCH-SUMMARY

- Delivered the exact requested theorem in `AKLT/W/H1M011/Main.lean`.
- The theorem compiles with `lake build AKLT.W.H1M011.Main`.
- `main` depends only on `propext`, `Classical.choice`, and `Quot.sound`.
- No existing project files were changed; only the assigned new Lean file and report were added.
- No open proof obligations or deviations.
