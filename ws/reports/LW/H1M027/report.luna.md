STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1M027/AKLT/W/H1M027/Main.lean)
- This report: `/home/ubuntu/aklt/reports/LW/H1M027/report.md`

## Delivered declarations

- `AKLT.W.H1M027.deletedLeafChoices`: from `PeripheralGeometry` and `LeafRule`, selects for every deleted site a positive normalizer and a replacement vector of squared norm at most one. The selected data satisfy the isolated-site identity and the one-bond radius identity for every surviving neighbor vector in the unit ball. The selection is made independently of `next`.
- `AKLT.W.H1M027.Residual_PeripheralLeafFactorization : Prop`: a closed residual. Given those sitewise local identities, it asks for the finite spin-sum reindexing and reduced-token placement, with the common normalizer fixed to the product of the site normalizers.
- `AKLT.W.H1M027.main_of_residual`: proves `AKLT.Blueprint.H1.PeripheralAssignmentStatement` assuming `Residual_PeripheralLeafFactorization`.

The requested unconditional declaration `AKLT.W.H1M027.main` is not proved.

## Axioms

`#print axioms AKLT.W.H1M027.deletedLeafChoices`:

```text
[propext, Classical.choice, Quot.sound]
```

`#print axioms AKLT.W.H1M027.main_of_residual`:

```text
[propext, Classical.choice, Quot.sound]
```

The latter theorem has the explicitly stated residual as a hypothesis; it is not a proof of the target by itself.

## Build

- Command: `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.H1M027.Main`
- Result: successful; module build reported 3.8 seconds (Lake completed in approximately 6 seconds).

## Open issue

`Residual_PeripheralLeafFactorization` remains unproved. It is the global bridge from local deleted-leaf identities to the separated sum: split assignments into retained/deleted spins, factor the deleted finite sums using the nonadjacency and unique-neighbor geometry, match retained factors, and assign replacement and unused tokens. The atom norm bounds needed at surviving spin arguments must be supplied in that proof. No counterexample to the target was found; this is an incomplete proof, not a false-status result.

## ORCH-SUMMARY

- Delivered a compiled local deleted-leaf choice theorem and the conditional bridge `main_of_residual`.
- The closed residual is `AKLT.W.H1M027.Residual_PeripheralLeafFactorization`.
- The required unconditional `AKLT.W.H1M027.main` is still open.
- The residual is the finite spin-sum factorization and token placement after local normalizers/vectors have been selected.
- Build: `lake build AKLT.W.H1M027.Main` succeeded.
- No existing files were edited.
- Orchestrator must discharge the residual or pass this leaf onward as partial.
