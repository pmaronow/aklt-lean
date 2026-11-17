STATUS: PROVED

## Files

- `AKLT/W/H1M004/Main.lean`

## Exported declaration

- `AKLT.W.H1M004.main : AKLT.Blueprint.H1.NormalizedMeanFactorStatement`

The proof defines `A` as the positive zero-bond mass and `u` as `localMean / ρ`. It proves the one-bond expansion by finite-sum linearity, uses the premise on `normSq (localMean s a)` to bound `u`, and identifies the first-moment coefficients with `A * localMean` using the positive denominator.

## Axiom audit

Command: `lake env lean /tmp/H1M004_axioms.lean`, where the script imports `AKLT.W.H1M004.Main` and runs `#print axioms AKLT.W.H1M004.main`.

Output:

```text
'AKLT.W.H1M004.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.H1M004.Main` — succeeded; the module compiled in 4.0s.

## Open issues

- None.

## ORCH-SUMMARY

- Delivered the requested theorem in `AKLT/W/H1M004/Main.lean`.
- Status: PROVED; requested Lake build succeeds.
- Axiom dependencies are `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements or deviations.
- No orchestrator decision is needed.
