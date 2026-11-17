STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC012/AKLT/W/REC012/Main.lean)

## Delivered declarations

- `AKLT.W.REC012.ResidualPinnedPartitionUpper : Prop` states the remaining summed comparison: for every `Departure`, the traced pinned partition is at most `12/5` times the original pinned partition.
- `AKLT.W.REC012.main : ResidualPinnedPartitionUpper → AKLT.Blueprint.Rec.PinnedRatioUpperStatement`. Thus the requested name is present, but its type has the explicit residual premise and is not the requested unconditional type.
- `AKLT.W.REC012.network_partition_nonneg` proves nonnegativity of any network partition from the concrete spin weights and unit-ball bounds.
- `AKLT.W.REC012.threeNeighbourScalarComparison` and `twoNeighbourScalarComparison` prove the local scalar comparisons from §6 for vectors in the unit ball. Supporting lemmas establish the icosahedral unit-vector bound and the required dot-product inequalities.

## Remaining work

The gap is lifting the pointwise local estimate through the two finite-network partition sums. This requires reindexing the active-spin assignments with the departure spin separated, showing that the rest of each integrand is a common nonnegative factor, and matching the incident bond factors in the pre-step and traced networks. These facts are not yet proved, so `ResidualPinnedPartitionUpper` remains open. No statement was identified as false or under-premised.

## Axioms

`#print axioms` was run for every exported theorem (`normSq_add`, `normSq_sub`, `normSq_nonneg'`, `dot_add_left`, `dot_abs_le_one`, `threeNeighbourLocalBounds`, `threeNeighbourScalarComparison`, `twoNeighbourLocalBound`, `twoNeighbourScalarComparison`, `goldenRatio_sq`, `icoRadius_sq`, `icoVector_normSq`, `spinVector_normSq_le_one`, `networkSpin_normSq_le_one`, `network_partition_nonneg`, `main_of_partition_comparison`, and `main`). Each produced the same output; representative lines:

```text
'AKLT.W.REC012.main' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.main_of_partition_comparison' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.network_partition_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.threeNeighbourScalarComparison' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC012.twoNeighbourScalarComparison' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.REC012.Main` — succeeded (first full module build: 7.8 s; final replay: 5.4 s). Lean emitted one deprecation warning for `if_pos` in the pinned-factor nonnegativity proof.
- The temporary axiom check used `PATH="$HOME/.elan/bin:$PATH" lake env lean /tmp/REC012_axioms.lean` and succeeded.

## ORCH-SUMMARY

- Delivered a compiled partial leaf at `AKLT/W/REC012/Main.lean`.
- `AKLT.W.REC012.main` is conditional on `AKLT.W.REC012.ResidualPinnedPartitionUpper`; it does not yet have the requested unconditional type.
- Proved partition nonnegativity and the local two- and three-neighbour scalar comparisons.
- Open exact residual: `AKLT.W.REC012.ResidualPinnedPartitionUpper`.
- No soundness escape hatches or nonstandard axioms were used; exported declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.
- Orchestrator must decide whether to pass this residual onward or continue the finite-sum reindexing and bond-factor comparison.
