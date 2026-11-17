STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_GAP016/AKLT/W/GAP016/Main.lean)
- `/home/ubuntu/aklt/reports/LW/GAP016/report.md`

## Exported declarations

- `productLaw_positiveProbability`: a product of positive normalized site laws is a positive normalized law, including the empty product.
- `poincare_of_subsingleton_configuration`: a normalized law on a subsingleton configuration space has Poincare lower bound 1.
- `emptyIndexTensorization`: the requested inequality for an empty site type. The configuration type is a singleton and the empty product has mass one.
- `subsingletonIndexTensorization` and `oneSiteIndexTensorization`: the requested inequality for a one-site index, with arbitrary finite nonempty alphabets and positive normalized site laws.
- `ProductTensorizationStatementV2_proved`: the requested inequality when the site cardinality is at most one.
- `ProductTensorizationSingletonAlphabetStatement_proved`: the requested inequality when every site alphabet is a subsingleton.
- `ProductTensorizationResidual`: the remaining inequality for site cardinality greater than one.
- `main (h : ProductTensorizationResidual) : AKLT.Blueprint.Gap.ProductTensorizationStatement`: combines the residual with the proved zero-site and one-site cases. **This is conditional and does not have the requested unconditional type.**

The residual is a transparent `def ... : Prop`; no unproved fact is treated as proved. The unresolved work is the finite product orthogonal projection/telescoping argument for two or more sites, including proving the coordinate projections commute and controlling their norms under the product law.

## Axiom checks

`#print axioms` for every exported theorem in `Main.lean` reports only the permitted axioms:

- `productLaw_positiveProbability`: `[propext, Classical.choice, Quot.sound]`
- `poincare_of_subsingleton_configuration`: `[propext, Classical.choice, Quot.sound]`
- `emptyIndexTensorization`: `[propext, Classical.choice, Quot.sound]`
- `subsingletonIndexTensorization`: `[propext, Classical.choice, Quot.sound]`
- `oneSiteIndexTensorization`: `[propext, Classical.choice, Quot.sound]`
- `main`: `[propext, Classical.choice, Quot.sound]`
- `ProductTensorizationStatementV2_proved`: `[propext, Classical.choice, Quot.sound]`
- `ProductTensorizationSingletonAlphabetStatement_proved`: `[propext, Classical.choice, Quot.sound]`

## Build

- Command: `export PATH="$HOME/.elan/bin:$PATH"; lake build AKLT.W.GAP016.Main`
- Result: successful; module build took about 3.6 seconds (Lake reported 8955/8955 jobs).

## Open issue

- `AKLT.W.GAP016.ProductTensorizationResidual` remains unproved. Consequently the required unconditional declaration `AKLT.W.GAP016.main : AKLT.Blueprint.Gap.ProductTensorizationStatement` is not delivered; the current `main` takes the residual as an explicit premise.

## ORCH-SUMMARY

- Compiled partial leaf: `AKLT/W/GAP016/Main.lean`.
- Proved product-law normalization and the Poincare inequality for zero or one site.
- Proved the all-singleton-alphabet special case and the at-most-one-site V2.
- Exact open proposition: `AKLT.W.GAP016.ProductTensorizationResidual` (product tensorization for site cardinality greater than one).
- `AKLT.W.GAP016.main` is conditional on that residual; the requested unconditional theorem signature is still open.
- Build succeeded with only permitted axioms: `propext`, `Classical.choice`, `Quot.sound`.
- No existing project files were changed.
