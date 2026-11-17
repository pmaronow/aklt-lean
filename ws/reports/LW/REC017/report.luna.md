STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC017/AKLT/W/REC017/Main.lean)

## Delivered declarations

- `AKLT.W.REC017.ResidualTwoFactorization : Prop` — the two-neighbour integrated partition factorization (`AKLT.Blueprint.Rec.TwoFactorizationStatement`).
- `AKLT.W.REC017.ResidualPositivePartitions : Prop` — strict positivity of the original and departure-removed partition sums for both pin choices.
- `AKLT.W.REC017.main_of_residuals (hFactor : ResidualTwoFactorization) (hPositive : ResidualPositivePartitions) : AKLT.Blueprint.Rec.TwoLogIdentityStatement`.

The conditional theorem derives positivity of both I₂ values, rewrites each step ratio as the reciprocal I₂, and applies the logarithmic divided-difference identity. Its proof handles coincident I₂ values by the diagonal branch of `logarithmicMean`.

## Axioms

`#print axioms AKLT.W.REC017.main_of_residuals`:

```text
'AKLT.W.REC017.main_of_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No forbidden proof placeholders or unsound declarations are used.

## Build

- `lake build AKLT.W.REC017.Main` — completed successfully; 12.3 seconds total (Lean module build reported 6.0 seconds).

## Open issues

- `AKLT.W.REC017.ResidualTwoFactorization` is not proved. It requires the finite sum reindexing and integration at the departure site, including the zero-mean post-step case.
- `AKLT.W.REC017.ResidualPositivePartitions` is not proved. It requires a strictly positive configuration for both the original and removed networks with arbitrary unit pins.
- Consequently the requested unconditional declaration `AKLT.W.REC017.main : AKLT.Blueprint.Rec.TwoLogIdentityStatement` is not delivered.

## ORCH-SUMMARY

- Delivered a compiled conditional proof of the requested identity in `AKLT/W/REC017/Main.lean`.
- The exact requested theorem `AKLT.W.REC017.main` remains open.
- Residuals: `AKLT.W.REC017.ResidualTwoFactorization`; `AKLT.W.REC017.ResidualPositivePartitions`.
- The factorization residual is the exact partition split; positivity residual is only the strict positivity needed for logs and division.
- `main_of_residuals` uses only `propext`, `Classical.choice`, and `Quot.sound`.
- Build command: `lake build AKLT.W.REC017.Main` (successful, 12.3 seconds).
- No user decision is needed; the orchestrator must supply proofs of both residuals or continue them as separate leaves.
