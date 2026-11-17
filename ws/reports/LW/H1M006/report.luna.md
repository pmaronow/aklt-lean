STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1M006/AKLT/W/H1M006/Main.lean)
- `/home/ubuntu/aklt/reports/LW/H1M006/report.md`

Only the new task-directory module was written. No frozen or existing project files were changed.

## Exported declarations

- `AKLT.W.H1M006.passageComplement`: the active sites with `(0,0)` erased.
- `AKLT.W.H1M006.originalSummand` and `erasedSummand`: one summand of the original and passage-erased functionals.
- `AKLT.W.H1M006.splitAssignments`: an equivalence splitting an active spin assignment into its passage atom and the assignment on the complement.
- `AKLT.W.H1M006.Residual_currentLocal` and `Residual_nextLocal`: explicit pointwise residual equalities. Each sums over the passage atom for a fixed complement assignment and equates that result to the corresponding erased summand with `passageI` or `passageJ`.
- `AKLT.W.H1M006.main_of_residuals`:
  `Residual_currentLocal → Residual_nextLocal → AKLT.Blueprint.H1.PassageFubiniStatement`.

The requested exact theorem `AKLT.W.H1M006.main : AKLT.Blueprint.H1.PassageFubiniStatement` is not yet proved. The compiled result proves the global finite-sum/reindexing step from the two local residuals.

## Axioms

`#print axioms AKLT.W.H1M006.main_of_residuals`:

```text
'AKLT.W.H1M006.main_of_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No forbidden proof escape appears in the delivered Lean file.

## Build

- `lake build AKLT.W.H1M006.Main` — succeeded; Lake reported 7.0 seconds for the module build (14 seconds wall time for the command).
- Axiom check: `lake env lean /tmp/H1M006Axioms.lean` — succeeded.

## Open issue

Prove `Residual_currentLocal` and `Residual_nextLocal` from the supplied one-site identities and `π.Covered`. This is the core local factorization: characterize the present bonds incident to `(0,0)`, show the next integrand drops the outgoing bond, and handle absent neighbours as zero in the passage-site moment formulas. Until those residuals are proved, the requested exact `main` declaration is unavailable.

## ORCH-SUMMARY

- Delivered a compiled assignment split and theorem `main_of_residuals` reducing `PassageFubiniStatement` to `Residual_currentLocal` and `Residual_nextLocal`.
- Open declarations: `AKLT.W.H1M006.Residual_currentLocal`, `AKLT.W.H1M006.Residual_nextLocal`; neither is proved.
- The exact requested declaration `AKLT.W.H1M006.main` is not delivered; status is PARTIAL.
- Module build succeeded; `main_of_residuals` uses only `propext`, `Classical.choice`, and `Quot.sound`.
- Orchestrator must finish the local bond characterization and passage-site sum for both current and next cases.
