STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_Q029/AKLT/W/Q029/Main.lean)
- This report: `/home/ubuntu/aklt/reports/LW/Q029/report.md`

## Delivered declarations

- `AKLT.W.Q029.pairZ_on_diag (m : Fin 9)` proves
  `pairZ (diagonalAdjointVector m.val) = ((4 : ℂ) - (m.val : ℂ)) • diagonalAdjointVector m.val`.
- `AKLT.W.Q029.ResidualPairTopSpan : Prop` is the remaining range statement that the nine weighted coefficient vectors span `(LinearMap.ker pairDiagonal)ᗮ`.
- `AKLT.W.Q029.ResidualAdjointEigenvectors : Prop` is the remaining assertion that each of those nine vectors lies in the eigenvalue-20 eigenspace.
- `AKLT.W.Q029.main` proves the requested blueprint inclusion **from both residuals**. Its actual type is
  `ResidualPairTopSpan → ResidualAdjointEigenvectors → AKLT.Blueprint.Q.PairTopInclusionStatement`,
  so it is not the requested unconditional leaf theorem.

`#print axioms` output:

```text
AKLT.W.Q029.pairZ_on_diag: [propext, Classical.choice, Quot.sound]
AKLT.W.Q029.main: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.Q029.Main` — passed, 8.59 seconds total (module compile reported 3.8 seconds).

## Open issues

- Prove `AKLT.W.Q029.ResidualPairTopSpan`, including the diagonal coefficient extraction and the rank/dimension argument.
- Prove `AKLT.W.Q029.ResidualAdjointEigenvectors`, completing the finite raising/lowering Casimir calculations with the square-root binomial factors.
- Replace the conditional `AKLT.W.Q029.main` with the required unconditional declaration `AKLT.W.Q029.main : AKLT.Blueprint.Q.PairTopInclusionStatement` after both residuals are discharged.

## ORCH-SUMMARY

- Delivered a compiled partial module with weighted diagonal vectors, the coordinate action formulas, and the total `J_z` action.
- The required unconditional theorem is not proved.
- Exact remaining declarations: `ResidualPairTopSpan`, `ResidualAdjointEigenvectors`.
- Conditional assembly: `AKLT.W.Q029.main hSpan hEigen`.
- `lake build AKLT.W.Q029.Main` passed in 8.59 seconds; reported axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
- Orchestrator should treat this as PARTIAL and not as a completed leaf proof.
