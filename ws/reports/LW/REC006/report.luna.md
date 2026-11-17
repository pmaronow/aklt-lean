STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC006/AKLT/W/REC006/Main.lean)
- `/home/ubuntu/aklt/reports/LW/REC006/report.md`

## Exported declarations

- `AKLT.W.REC006.ResidualFreePairNumeratorStatement`: for every departure and distinct pair of present neighbours, the unnormalized free pair numerator in `removeSite` is nonnegative.
- `AKLT.W.REC006.ResidualFreeNormalizerStatement`: for every departure, the free partition normalizer in `removeSite` is strictly positive.
- `AKLT.W.REC006.main_from_residuals (hNumerator) (hNormalizer) : AKLT.Blueprint.Rec.FreeRemovedPairStatement`.

The exact requested theorem `AKLT.W.REC006.main` is not delivered because the residuals remain unproved. The numerator residual isolates the degree-four free positivity step; the normalizer residual isolates positivity of the denominator.

## Axiom audit

`#print axioms AKLT.W.REC006.main_from_residuals`:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.REC006.Main` — succeeded, 12.2 s wall time (Lean module build reported 4.9 s).

## Open issues

- Prove `AKLT.W.REC006.ResidualFreePairNumeratorStatement` from the concrete degree-four free positivity argument.
- Prove `AKLT.W.REC006.ResidualFreeNormalizerStatement` from the concrete free partition positivity argument.
- Then export `AKLT.W.REC006.main` at the exact requested type.

## ORCH-SUMMARY

- Delivered a compiled conditional proof in `AKLT/W/REC006/Main.lean`.
- `AKLT.W.REC006.main_from_residuals` proves the requested blueprint proposition from the two explicit residuals.
- Open residuals: `AKLT.W.REC006.ResidualFreePairNumeratorStatement` and `AKLT.W.REC006.ResidualFreeNormalizerStatement`.
- The exact theorem `AKLT.W.REC006.main` is not yet proved; status is PARTIAL.
- Build command: `lake build AKLT.W.REC006.Main` (succeeded).
- The exported conditional theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.
