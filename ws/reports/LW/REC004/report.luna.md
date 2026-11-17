STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC004/AKLT/W/REC004/Main.lean)

## Delivered declarations

- `AKLT.W.REC004.Residual_ThreePairSum`: the two-sided `[-27/50, 27/25]` bound for the sum of the three removed-network pair means, under the target's departure and neighbour hypotheses.
- `AKLT.W.REC004.Residual_OnePair`: the two-sided `[-9/25, 9/25]` bound for the `f,g` pair mean.
- `AKLT.W.REC004.Residual_FreePairs`: nonnegativity of the three free pair means used by the final comparison.
- `AKLT.W.REC004.main_from_residuals (hSum) (hPair) (hFree) : AKLT.Blueprint.Rec.RemovedMeanIntervalsStatement`.

The last theorem derives all four `responseI`/`responseJ` intervals and both free-choice inequalities by exact linear arithmetic. The requested unconditional theorem `AKLT.W.REC004.main : AKLT.Blueprint.Rec.RemovedMeanIntervalsStatement` is not delivered because the three residuals are still open.

## Axioms

`#print axioms AKLT.W.REC004.main_from_residuals`:

```text
'AKLT.W.REC004.main_from_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the permitted Lean axioms. The residuals are definitions of propositions, not axioms or theorem hypotheses embedded into a claimed unconditional result.

## Build

- Command: `lake build AKLT.W.REC004.Main`
- Result: successful; full command elapsed 15.49 s, Lean module build reported 6.7 s.

## Open issues

- `Residual_ThreePairSum` needs the finite-network reindexing and conditioning proof: split each configuration into fibres over all other active spins, handle zero-mass fibres separately, factor the positive fibres over the three nonadjacent neighbours, and apply the three-factor mean bound.
- `Residual_OnePair` needs the same fibre argument and the norm bound `3/5` on each conditional spin mean.
- `Residual_FreePairs` needs free degree-four positivity for the pair insertion after deleting the departure site, with the active sites reindexed into the common finite-network model.
- Thus the exact requested `main` theorem remains open. No coefficient or logarithmic-mean claims are part of this frozen target's type.

## ORCH-SUMMARY

- Delivered one compiled conditional assembly in `AKLT/W/REC004/Main.lean`.
- Exact target theorem `AKLT.W.REC004.main` remains open.
- Open residuals: `Residual_ThreePairSum`, `Residual_OnePair`, `Residual_FreePairs`.
- `main_from_residuals` derives the target from those three pair-mean facts.
- Build: `lake build AKLT.W.REC004.Main` succeeded; 15.49 s elapsed.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- The orchestrator must supply or prove the three stated finite-network residuals before claiming this leaf complete.
