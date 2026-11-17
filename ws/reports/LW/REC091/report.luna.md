STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC091/AKLT/W/REC091/Main.lean)

## Delivered declarations

- `Residual_SharedCoverMixture : Prop` — the common nonnegative pattern mixture for the current and post-step pinned partitions.
- `Residual_StepFactorizations : Prop` — the two- and three-neighbour departure integration identities.
- `Residual_RemovedPartitionPositive : Prop` — positivity of the pinned partition after removing the departure site.
- `Residual_PartitionLower : Prop` — H1's shared-mixture partition comparison before departure integration.
- `partitionLower_of_sharedCoverMixture (hMix) : Residual_PartitionLower` — applies H1 term by term using the same `localThreshold` and the canonical `patternCurrent`/`patternNext` definitions.
- `main_of_residuals (hLower) (hFact) (hPos) : AKLT.Blueprint.Rec.CoveredIntegratedLowerStatementV2` — derives both requested response inequalities by integrating and cancelling the positive removed partition.
- `main_from_core_residuals (hMix) (hFact) (hPos) : AKLT.Blueprint.Rec.CoveredIntegratedLowerStatementV2` — combines the mixture comparison with the integration step.

The exact closed declaration `AKLT.W.REC091.main : AKLT.Blueprint.Rec.CoveredIntegratedLowerStatementV2` is not delivered because the three core residual propositions below remain unproved.

## Axioms

`#print axioms` output for each exported theorem:

```text
partitionLower_of_sharedCoverMixture: [propext, Classical.choice, Quot.sound]
main_of_residuals: [propext, Classical.choice, Quot.sound]
main_from_core_residuals: [propext, Classical.choice, Quot.sound]
```

No forbidden proof placeholders or axioms are used.

## Build

- `lake build AKLT.W.REC091.Main` — passed; command wall time 12.5 s, target module build 4.8 s.

## Open issues

- `Residual_SharedCoverMixture`: needs the finite outside-spin disintegration, tip replacement, and corner-slot convex expansion for the shared internal-bond cover. No proved theorem supplying this mixture is available in the worktree.
- `Residual_StepFactorizations`: needs the exact two- and three-neighbour integration identities for `Network.partition` and `traceStep`.
- `Residual_RemovedPartitionPositive`: needs positivity of the removed-site network partition for every `Departure`; the relevant finite-spin facts are stated as blueprint obligations but are not available here as proved lemmas.

## ORCH-SUMMARY

- Delivered a compiled conditional reduction in `AKLT/W/REC091/Main.lean`.
- H1 plus `Residual_SharedCoverMixture` proves `Residual_PartitionLower` by termwise comparison with the unchanged threshold and canonical pattern sums.
- `main_of_residuals` proves the exact target from `Residual_PartitionLower`, `Residual_StepFactorizations`, and `Residual_RemovedPartitionPositive`.
- Open exact residuals: `AKLT.W.REC091.Residual_SharedCoverMixture`, `AKLT.W.REC091.Residual_StepFactorizations`, and `AKLT.W.REC091.Residual_RemovedPartitionPositive`.
- The exact declaration `AKLT.W.REC091.main` remains open; no counterexample was found.
- Build passed with only allowed axioms (`propext`, `Classical.choice`, `Quot.sound`).
- Orchestrator decision: assign/prove the three residuals or route this leaf to an existing proved local-mixture/integration/positivity library.
