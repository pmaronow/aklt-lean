STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_Q030/AKLT/W/Q030/Main.lean)

## Declarations

- `AKLT.W.Q030.weightSpace (r : Fin 9)`: span of pair basis vectors with total weight `r`.
- `AKLT.W.Q030.weightBlock (r : Fin 9)`: intersection of that weight space with the eigenvalue-20 eigenspace.
- `AKLT.W.Q030.ResidualWeight0` through `ResidualWeight8`: the nine claims that the corresponding weight block has finrank one. Their block sizes are `1,2,3,4,5,4,3,2,1`.
- `AKLT.W.Q030.ResidualWeightDecomposition`: the structural claim that the top eigenspace's finrank is the sum of the nine block finranks.
- `AKLT.W.Q030.main_of_residuals`: proves `AKLT.Blueprint.Q.PairTopDimensionStatement` from those ten explicit residual statements.

The requested closed declaration `AKLT.W.Q030.main : AKLT.Blueprint.Q.PairTopDimensionStatement` is not proved yet. I did not assume any residual statement in a theorem claiming the original result.

## Axioms

`#print axioms AKLT.W.Q030.main_of_residuals`:

```text
'AKLT.W.Q030.main_of_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.Q030.Main` — succeeded; module compile reported 6.7 s (16.5 s command wall time including Lake startup/build bookkeeping).
- `lake env lean /tmp/Q030Audit.lean` — succeeded; printed the axiom list above.

## Open issues

The nine residual block dimensions still need exact proofs from the concrete spin matrices. The decomposition residual still needs a proof that the eigenvalue-20 eigenspace splits across total weights. No numerical eigensolver or inferred multiplicity was used.

## ORCH-SUMMARY

- Delivered a compiling partial module at `AKLT/W/Q030/Main.lean`.
- Proved `main_of_residuals`, reducing the requested dimension statement to nine small block-dimension claims and one structural decomposition claim.
- Open declarations: `ResidualWeight0`–`ResidualWeight8`, `ResidualWeightDecomposition`.
- The exact requested theorem `AKLT.W.Q030.main` remains open.
- Build succeeded with `lake build AKLT.W.Q030.Main`.
- Exported theorem axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
- No existing files were changed; no numerical solver was used.
