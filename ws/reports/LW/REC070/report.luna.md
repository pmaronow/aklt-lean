STATUS: PARTIAL

## Files

- `AKLT/W/REC070/Main.lean`

## Delivered declarations

- `AKLT.W.REC070.geometricBudget_proved : AKLT.W.REC070.Residual_GeometricBudget`
  Proves the explicit weighted geometric-series budget using
  `∑' n, n(n+1)r^n = 2r/(1-r)^3`.
- `AKLT.W.REC070.main_of_residuals : Residual_RowExpansion → Residual_LengthIncrement → AKLT.Blueprint.Rec.WitnessPerturbationStatement`
  Completes the witness transport from the two stated residuals, the given unshifted row inequality, and the explicit epsilon budget.

The requested theorem `AKLT.W.REC070.main` with no residual hypotheses is not delivered. The file contains no `sorry`, `admit`, or added axioms.

## Residuals

- `Residual_RowExpansion` states that the weighted shifted row equals the ENNReal tsum of its finite length contributions `RowLength`. It is smaller than the target because it is an identity, with no contraction or perturbation inequality. It remains to prove nonnegative regrouping and that coefficients outside `Finset.range (n + 2)` vanish.
- `Residual_LengthIncrement` states, at each fixed length `n`, that `RowLength θ X n ≤ RowLength 1 X n + RowLengthError CV q θ X n`. It is smaller than the target because it has no infinite length sum and makes no row contraction claim. Its proof still needs the first-visit ordering and product comparison, nonnegative coefficient support, the closed-trail shift bound, the per-departure coefficient envelope, and the H2 comparison with open trails.
- `Residual_GeometricBudget` is also defined explicitly and is discharged by `geometricBudget_proved`; it is not an open residual.

The assumed unshifted inequality in the target is used directly as a numerical bound on the `θ = 1` weighted row. No H3 leaf proposition is assumed.

## Axioms

`#print axioms AKLT.W.REC070.geometricBudget_proved`:

```text
'AKLT.W.REC070.geometricBudget_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`#print axioms AKLT.W.REC070.main_of_residuals`:

```text
'AKLT.W.REC070.main_of_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.REC070.Main` — passed; Lean reported 6.6 s for the module build (12.2 s command elapsed).

## Open issues

Prove `AKLT.W.REC070.Residual_RowExpansion` and `AKLT.W.REC070.Residual_LengthIncrement` from their definitions and `OpenTrailBound`. Once supplied, `main_of_residuals` yields the requested statement; the exact theorem `AKLT.W.REC070.main` remains to be added.

## ORCH-SUMMARY

- Delivered `AKLT/W/REC070/Main.lean` and this report.
- Proved the geometric transport budget and the final implication from two explicit residuals.
- Open residuals: `AKLT.W.REC070.Residual_RowExpansion`; `AKLT.W.REC070.Residual_LengthIncrement`.
- The exact declaration `AKLT.W.REC070.main` is not yet delivered.
- No source files outside the task directory were edited; no axioms or placeholders were added.
- Build command: `lake build AKLT.W.REC070.Main` (passed).
- Orchestrator should continue with row regroup/support and the per-length H2 bound, then specialize `main_of_residuals`.
