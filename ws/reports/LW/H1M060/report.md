STATUS: PROVED

## Files

- `AKLT/W/H1M060/Main.lean`
- `/home/ubuntu/aklt/reports/LW/H1M060/report.md`

## Exported declaration

`AKLT.W.H1M060.main : AKLT.Blueprint.H1.InversionBallStatementV2`, where

```lean
AKLT.Blueprint.H1.InversionBallStatementV2 :=
  ∀ n : ℕ, ∀ I : Finset (Fin n), ∀ u : Fin n → AKLT.Defs.Vec3, ∀ j : Fin n,
    AKLT.Defs.normSq (AKLT.Defs.invertVectorsReal I u j) = AKLT.Defs.normSq (u j)
```

The proof splits on `j ∈ I`. In either branch, unfolding vector inversion, `normSq`,
and `dot` reduces the goal to equality of the same coordinate-square sum; simplification
handles negation in each coordinate.

## Axioms

`#print axioms AKLT.W.H1M060.main`:

```text
'AKLT.W.H1M060.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.H1M060.Main`
- Result: successful; module built in 3.6 s, total elapsed 8.28 s.

## Open issues

None.

## ORCH-SUMMARY

- Delivered the proof at `AKLT/W/H1M060/Main.lean` with the requested theorem name and type.
- The theorem compiles and has only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements, deviations, or open issues.
