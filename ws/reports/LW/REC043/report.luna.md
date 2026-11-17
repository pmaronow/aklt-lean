STATUS: PARTIAL

## Files

- Added [`Main.lean`](/home/ubuntu/aklt/wt/LW_REC043/AKLT/W/REC043/Main.lean).
- No existing project files were changed.

## Delivered declarations

- `AKLT.W.REC043.PairCoordinateExpansionResidual : Prop` is the coordinate-wise stopped-trail expansion for one coordinate `k : Fin 3`, for either pin choice and all admissible input networks. It isolates the moving-coordinate iteration, including its trace coefficients and trace ratios.
- `AKLT.W.REC043.main_of_pairCoordinateExpansionResidual (hResidual : PairCoordinateExpansionResidual) : AKLT.Blueprint.Rec.PairExpansionStatement` proves the requested pair expansion from that residual. The proof uses linearity of the finite partition sum, the finite stopped-trail sum, and `dot` as the sum over three coordinates.

The requested closed theorem `AKLT.W.REC043.main : AKLT.Blueprint.Rec.PairExpansionStatement` is not yet proved. The remaining blocker is proving `PairCoordinateExpansionResidual`: one must establish the finite-degree site moment step for each moving coordinate, preserve the original-leg factors and live target, and iterate over unused bonds while handling dead branches. The target, coefficient, and ratio definitions are the ones in `AKLT/Defs/Domain.lean` and `AKLT/Blueprint/Rec/Definitions.lean`; no other blueprint leaf was used as a lemma.

## Axioms

`#print axioms AKLT.W.REC043.main_of_pairCoordinateExpansionResidual`:

```text
'AKLT.W.REC043.main_of_pairCoordinateExpansionResidual' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.REC043.Main`
- Result: success; Lean reported the module build in 5.0 seconds (10.4 seconds elapsed for the Lake command).
- Axiom audit: `lake env lean /tmp/REC043Axioms.lean` succeeded.

## Open issue

Prove `AKLT.W.REC043.PairCoordinateExpansionResidual`, then export the exact requested `AKLT.W.REC043.main` theorem. No false-premise issue was found; the work is incomplete rather than a counterexample.

## ORCH-SUMMARY

- Delivered a compiled coordinate-linearity reduction in `AKLT/W/REC043/Main.lean`.
- Exact residual: `AKLT.W.REC043.PairCoordinateExpansionResidual`.
- Conditional theorem: `AKLT.W.REC043.main_of_pairCoordinateExpansionResidual` proves the requested statement from that residual.
- Open: prove the coordinate-wise moving-mark expansion by local moments and finite unused-bond induction.
- Limitation: exact declaration `AKLT.W.REC043.main` is not yet available; status is PARTIAL.
- The orchestrator should pass the residual proof task on or decide whether to continue this leaf.
