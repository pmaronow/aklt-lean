STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1C021/AKLT/W/H1C021/Main.lean)

## Declarations

- `AKLT.W.H1C021.Residual_vacuumTransfer`: closed proposition asserting the empty-code ring contraction equals the rational Pauli sector entry of the polynomial ring product.
- `AKLT.W.H1C021.Residual_centerTransfer`: closed proposition asserting the summed center-insertion contractions equal the corresponding rational Pauli sector entry.
- `AKLT.W.H1C021.main_of_residuals (hzero : Residual_vacuumTransfer) (hcenter : Residual_centerTransfer) : AKLT.Cert.H1.Production.Leaves.tensorSubstitution`.

The exact closed declaration `AKLT.W.H1C021.main : AKLT.Cert.H1.Production.Leaves.tensorSubstitution` is not delivered. The conditional theorem proves that the two stated transfer obligations suffice; neither obligation is assumed inside an unconditional theorem.

## Axiom audit

`#print axioms AKLT.W.H1C021.main_of_residuals`:

```text
'AKLT.W.H1C021.main_of_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.H1C021.Main` — succeeded; 12.552 seconds wall time, target module built in 6.3 seconds.

## Open issues

- `Residual_vacuumTransfer` needs the sitewise Pauli/table equality for the no-insertion ring product.
- `Residual_centerTransfer` needs that equality distributed over the center color choices and summed over center pairs.
- These are the hard unresolved steps: derive the local transfer from `tableCheck`, align mixed-radix basis digits with the exchange basis, and preserve the `Y` imaginary signs and the unnormalized norms (including the exterior factor).
- The residuals are transparent closed propositions and are strictly narrower than the original leaf: each handles only one part of the network numerator. The finite-sum and scalar linearity needed to assemble them is proved in `Main.lean`.

## ORCH-SUMMARY

- Delivered `AKLT/W/H1C021/Main.lean` and a successful module build.
- Proved `main_of_residuals` from `Residual_vacuumTransfer` and `Residual_centerTransfer`.
- Open declarations: `AKLT.W.H1C021.Residual_vacuumTransfer` and `AKLT.W.H1C021.Residual_centerTransfer`.
- The requested unconditional `AKLT.W.H1C021.main` remains open.
- The blocker is the local Pauli/table-to-polynomial transfer, including index alignment and exact complex signs/scales.
- No existing project files were modified; no soundness escape hatches were used.
