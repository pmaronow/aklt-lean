STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_GAP026/AKLT/W/GAP026/Main.lean`
- `/home/ubuntu/aklt/reports/LW/GAP026/report.md`

## Exported declaration

- `AKLT.W.GAP026.main : AKLT.Blueprint.Gap.ProductCouplingTransportStatement`

The proof pulls the given coupling back through `e.configurations` in each component. The `Carries` hypotheses give the pulled-back marginals. A private lemma uses `coordinate_eq` and the site equivalence to prove exact equality of Hamming counts; reindexing both finite sums then gives exact equality of coupling costs.

## Axioms

`#print axioms main` reports:

```text
[propext, Classical.choice, Quot.sound]
```

No additional axioms are used.

## Build

- Command: `lake build AKLT.W.GAP026.Main`
- Result: successful
- Wall time for the successful build invocation: 8.8 seconds

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.GAP026.main` with the requested statement.
- Pullback uses the same configuration equivalence in both coupling coordinates.
- `coordinate_eq` proves exact Hamming equality, so coupling costs are equal.
- Build succeeded with only `propext`, `Classical.choice`, and `Quot.sound`.
- No helper files, residual statements, or known limitations.
