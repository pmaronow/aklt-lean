STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_WIN049/AKLT/W/WIN049/Main.lean`
- `/home/ubuntu/aklt/reports/LW/WIN049/report.md`

## Exported declaration

`AKLT.W.WIN049.main : AKLT.Blueprint.Win.PartLawBridgeStatement`

The proof shows the `partWeight` sum equals the supplied partition normalizer. `MomentsStatement` supplies unit norm for each `icoVector`; the pin assignment supplies unit norm for pins. Squared-norm nonnegativity then gives nonnegative bond factors, so normalizing `partWeight` gives a probability. Distributing the positive normalizer through the finite sum identifies its expectation with `partMean`.

## Axioms

`#print axioms AKLT.W.WIN049.main`:

```text
'AKLT.W.WIN049.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.WIN049.Main` — succeeded; Lean reported the module built in 6.5 s.
- `lake env lean /tmp/WIN049Axioms.lean` — succeeded and printed the axiom list above.

## Open issues

None. The build emitted two deprecation warnings for `if_pos` and `if_neg`; they do not affect the proof or build.

## ORCH-SUMMARY

- Delivered the exact theorem `AKLT.W.WIN049.main` in `AKLT/W/WIN049/Main.lean`.
- The theorem proves `AKLT.Blueprint.Win.PartLawBridgeStatement` from its stated `MomentsStatement` and denominator positivity hypothesis.
- Build succeeded with the requested Lake command.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements, deviations, or open proof obligations remain.
