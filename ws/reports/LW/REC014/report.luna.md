STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC014/AKLT/W/REC014/Main.lean)

## Exported declaration

- `AKLT.W.REC014.main_of_residuals`:
  `AKLT.W.REC014.ResidualPartitionCollapse →
   AKLT.W.REC014.ResidualPartitionPositive →
   AKLT.Blueprint.Rec.OneStepTrivialStatement`

The requested unconditional declaration `AKLT.W.REC014.main` is not proved.
The delivered theorem reduces the ratio conclusion to these explicit closed
residual propositions:

- `AKLT.W.REC014.ResidualPartitionCollapse`: under the one-neighbour U-site
  hypotheses, each pinned or free partition is unchanged by the trace step.
- `AKLT.W.REC014.ResidualPartitionPositive`: under those hypotheses, each
  original partition is strictly positive, so division by it gives one.

The local partition-collapse proof still needs to split off the departure spin
from the finite assignment sum, show its only interaction is the outgoing bond,
and account for the unchanged original-leg factors. The positivity residual
needs a positive-mass configuration for the auxiliary finite network. Neither
residual is assumed or proved in the file.

## Axiom audit

`#print axioms AKLT.W.REC014.main_of_residuals`:

```text
'AKLT.W.REC014.main_of_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.REC014.Main`
- Result: successful; Lean reported `Built AKLT.W.REC014.Main (4.5s)`.

## Open issues

- Prove `AKLT.W.REC014.ResidualPartitionCollapse` from `Departure`, `Auxiliary`,
  the U status, and one-present-neighbour hypotheses.
- Prove `AKLT.W.REC014.ResidualPartitionPositive` from the same hypotheses.
- Then export the unconditional theorem as
  `AKLT.W.REC014.main : AKLT.Blueprint.Rec.OneStepTrivialStatement`.

## ORCH-SUMMARY

- Delivered a compiled ratio reduction in `AKLT/W/REC014/Main.lean`.
- `main_of_residuals` proves the requested statement from two explicit residual Props.
- Open: `AKLT.W.REC014.ResidualPartitionCollapse` and `AKLT.W.REC014.ResidualPartitionPositive`.
- The exact unconditional `AKLT.W.REC014.main` declaration remains open.
- Build passed with `lake build AKLT.W.REC014.Main` (4.5s).
- Axiom audit: `[propext, Classical.choice, Quot.sound]` for `main_of_residuals`.
- No existing project files were modified.
