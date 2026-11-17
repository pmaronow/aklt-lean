STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC013/AKLT/W/REC013/Main.lean)

## Delivered declarations

- `AKLT.W.REC013.Residual_DStepPartitionEquality`: for a departure whose site has status D, deleting the step leaves the pinned and free partition sums equal.
- `AKLT.W.REC013.Residual_AuxiliaryPartitionPositive`: every auxiliary network has a strictly positive pinned and free partition normalizer.
- `AKLT.W.REC013.main_of_residuals`:
  ```lean
  (hEq : Residual_DStepPartitionEquality) →
  (hPos : Residual_AuxiliaryPartitionPositive) →
  AKLT.Blueprint.Rec.DStepTrivialStatement
  ```
  The requested unconditional `AKLT.W.REC013.main` is not proved.

## Axiom audit

`#print axioms AKLT.W.REC013.main_of_residuals` reports:

```text
[propext, Classical.choice, Quot.sound]
```

The conditional theorem uses no extra axioms beyond these allowed ones. No forbidden proof placeholders or axioms are present.

## Build

- `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.REC013.Main` — succeeded; Lean module build reported 5.3 s (10.6 s wall time including Lake).

## Open issues

- Prove `AKLT.W.REC013.Residual_DStepPartitionEquality`. This is the finite-network reindexing and one-site D-spin integration step; the departure hypotheses provide the D status and one-bond restriction, while the original-leg exclusion still has to be used in the partition expansion.
- Prove `AKLT.W.REC013.Residual_AuxiliaryPartitionPositive`. This requires positivity of the finite pinned/free partition normalizers for arbitrary auxiliary networks; the relevant blueprint statement is not a proved dependency.
- Then expose the requested unconditional theorem as `AKLT.W.REC013.main` with exact type `AKLT.Blueprint.Rec.DStepTrivialStatement`.

## ORCH-SUMMARY

- Delivered a compiled conditional reduction in `AKLT/W/REC013/Main.lean`.
- Exact requested theorem remains open: `AKLT.W.REC013.main`.
- Residual obligations: `Residual_DStepPartitionEquality`, `Residual_AuxiliaryPartitionPositive`.
- `main_of_residuals` proves the requested conclusion from those explicit Props.
- Axiom audit: `[propext, Classical.choice, Quot.sound]`.
- Build command succeeded; see timing above.
- No frozen or existing project files were edited.
