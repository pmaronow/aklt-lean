STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC005/AKLT/W/REC005/Main.lean)

## Exported declarations

- `AKLT.W.REC005.Residual_PinnedPairMean : Prop` — for each admissible two-neighbour departure and either pin choice, the deleted-network pair mean lies in `[-9/25, 9/25]`.
- `AKLT.W.REC005.Residual_FreePairMean : Prop` — the free deleted-network pair mean is nonnegative.
- `AKLT.W.REC005.main_of_residuals (hp : Residual_PinnedPairMean) (hf : Residual_FreePairMean) : AKLT.Blueprint.Rec.TwoMeanIntervalsStatement` — proves the requested interval and free lower bound from those two pair-mean residuals.

The exact requested `AKLT.W.REC005.main` declaration is not delivered because the two finite-network estimates remain open. The residuals are closed propositions and split out the pinned interval and free positivity parts of the pair estimate.

## Axioms

`#print axioms AKLT.W.REC005.main_of_residuals`:

```text
'AKLT.W.REC005.main_of_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.REC005.Main` — completed successfully; Lake reported the module built in 6.2 seconds (8953 jobs).

## Open issues

- Prove `AKLT.W.REC005.Residual_PinnedPairMean`: reindex the active spins into the finite-network model, condition on all spins except the two neighbours, sum only positive-mass fibres, and apply the three-factor mean estimate to both conditional means.
- Prove `AKLT.W.REC005.Residual_FreePairMean`: establish degree-four free positivity for the pair observable in the deleted network.
- Then define the exact requested theorem `AKLT.W.REC005.main` without residual hypotheses.

## ORCH-SUMMARY

- Delivered a compiled reduction from two explicit pair-mean residuals to `TwoMeanIntervalsStatement`.
- No exact `AKLT.W.REC005.main` theorem is proved.
- Open residuals: `Residual_PinnedPairMean`, `Residual_FreePairMean`.
- `main_of_residuals` uses only the allowed axioms `[propext, Classical.choice, Quot.sound]`.
- Build: `lake build AKLT.W.REC005.Main` succeeded.
- The orchestrator must obtain proofs of both residuals or continue the finite-conditioning and free-positivity arguments.
