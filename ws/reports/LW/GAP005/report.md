STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_GAP005/AKLT/W/GAP005/Main.lean`
- `/home/ubuntu/aklt/reports/LW/GAP005/report.md`

## Exported declaration

`AKLT.W.GAP005.main : AKLT.Blueprint.Gap.CouplingMarginalTVStatement`

The theorem proves that every coupling of finite probabilities has disagreement mass at least their half-L1 total variation, and that pushing both laws through any deterministic map cannot increase total variation. The proof uses the coupling marginal equations, nonnegative masses, finite-sum triangle inequality, and regrouping finite sums.

## Axioms

`#print axioms AKLT.W.GAP005.main`:

```text
'AKLT.W.GAP005.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.GAP005.Main` — succeeded; final run completed in 9.5 seconds wall time (Lean module: 4.0 seconds).

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/GAP005/Main.lean` with the exact requested theorem name and type.
- Proved both coupling disagreement lower bound and deterministic marginalization TV contraction directly from the definitions.
- Build succeeded with `lake build AKLT.W.GAP005.Main`.
- Axiom footprint: `propext`, `Classical.choice`, `Quot.sound`.
- No residual statements, deviations, or open issues.
