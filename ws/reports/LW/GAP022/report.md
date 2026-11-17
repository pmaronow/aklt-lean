STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_GAP022/AKLT/W/GAP022/Main.lean`
- `/home/ubuntu/aklt/reports/LW/GAP022/report.md`

## Exported declaration

- `AKLT.W.GAP022.main : AKLT.Blueprint.Gap.LipschitzEigenvalueStatement`

The proof shows that a nonzero mean-zero eigenfunction cannot be constant, so its finite edge seminorm is positive. A coordinate-update path then gives a differing one-coordinate edge. The proof establishes nonnegative homogeneity of the edge supremum, applies the contraction premise to the eigenfunction, and cancels the positive seminorm when the eigenvalue is positive. Nonpositive eigenvalues satisfy the conclusion from `r ≥ 0`.

## Axioms

`#print axioms AKLT.W.GAP022.main`:

```text
[propext, Classical.choice, Quot.sound]
```

These are the allowed axioms. No residual statements or forbidden proof constructs are used.

## Build

- Command: `lake build AKLT.W.GAP022.Main`
- Result: succeeded; module build reported 3.8 seconds.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.GAP022.main` with the requested exact type in `AKLT/W/GAP022/Main.lean`.
- The target module builds successfully.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- No residual declarations, deviations, or open issues.
