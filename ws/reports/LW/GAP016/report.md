STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_GAP016/AKLT/W/GAP016/Main.lean:45): required unconditional theorem and the complex-component identities.
- [Product.lean](/home/ubuntu/aklt/wt/LW_GAP016/AKLT/W/GAP016/Product.lean): product normalization, splitting finite product sums, coordinate averages and their commutation.
- [RealTensorization.lean](/home/ubuntu/aklt/wt/LW_GAP016/AKLT/W/GAP016/RealTensorization.lean): orthogonal decomposition, contraction and tensorization for real functions.
- [Conditioning.lean](/home/ubuntu/aklt/wt/LW_GAP016/AKLT/W/GAP016/Conditioning.lean): identification of the given singleton conditional-expectation quotient with coordinate averaging.
- [Audit.lean](/home/ubuntu/aklt/wt/LW_GAP016/AKLT/W/GAP016/Audit.lean): exact closed-type check and axiom checks for all 27 exported theorems.
- [build.log](/home/ubuntu/aklt/reports/LW/GAP016/build.log) and [axioms.log](/home/ubuntu/aklt/reports/LW/GAP016/axioms.log): successful validation logs.

## Required declaration

```lean
theorem AKLT.W.GAP016.main :
    AKLT.Blueprint.Gap.ProductTensorizationStatement
```

This has no residual argument or extra premise. The explicit check in `Audit.lean` is:

```lean
example : AKLT.Blueprint.Gap.ProductTensorizationStatement := AKLT.W.GAP016.main
```

## Proof

The proof uses the frozen statement and its definitions, plus Mathlib. It assumes no other blueprint leaf.

For real functions, define the coordinate average `A_i` by summing over the letter at site `i`. Splitting the product sum shows that this average preserves expectation. The coordinate averages commute, and their squared weighted norms satisfy Pythagoras. Consequently each average is a contraction, and averaging at one site cannot increase any other site's energy.

Induct on the finite set of coordinates on which a function depends. Averaging at the inserted coordinate removes that dependence and splits the variance into its site energy plus the variance of the averaged function. Apply the induction hypothesis and energy contraction. At the empty set, the function is constant and its variance is zero. This includes zero sites: the empty product is normalized on the one-point configuration space.

Finally, singleton fibres are parametrized by updating one letter. Factoring their masses and cancelling the strictly positive exterior product identifies the statement's conditional-expectation quotient with `A_i`. Splitting complex squared norms into real and imaginary squares and adding the two real inequalities proves `main`.

## Exported declarations and statements

Every name below has prefix `AKLT.W.GAP016.`. The site type is finite with decidable equality, and the alphabets are dependent finite types. The statement's nonempty-alphabet instances are retained by `main`.

Notation for the tables:

- `p(σ) = productMass π σ = ∏ i, π i (σ i)`.
- `A_i f(σ) = average π i f σ = ∑ a, π i a * f(update σ i a)`.
- `M(f) = realMean π f = ∑ σ, p(σ) * f(σ)`.
- `Q(f) = squareMass π f = ∑ σ, p(σ) * f(σ)^2`.
- `V(f) = realVariance π f = Q(f - M(f))`.
- `D_i(f) = siteEnergy π i f = Q(f - A_i f)`.
- `e_i = Equiv.piSplitAt i S`, identifying configurations with a letter and the remaining coordinates.
- `N` means `∀ i, ∑ a, π i a = 1`; `P` means `∀ i, PositiveProbability (π i)`.
- `A_i^C` uses complex casts of the real site weights. `f.re` and `f.im` denote pointwise components.

The six transparent definitions exported are `productMass`, `average`, `squareMass`, `realMean`, `realVariance`, and `siteEnergy`, with the defining formulas above. Generic product and averaging identities below work over an arbitrary commutative semiring `R`; order, subtraction and variance statements use real weights and real functions unless complex functions are specified.

| Theorem | Additional assumptions | Statement |
| --- | --- | --- |
| `productLaw_positiveProbability` | P | `PositiveProbability (productMass π)` |
| `productMass_update` | None | `p(update σ i a) = π i a * ∏ j ∈ univ.erase i, π j (σ j)` |
| `split_update` | None | `update (e_i.symm (a,r)) i b = e_i.symm (b,r)` |
| `productMass_split` | None | `p(e_i.symm (a,r)) = π i a * ∏ j : {j // j ≠ i}, π j (r j)` |
| `sum_productMass_split` | None | `∑ σ, p(σ)*f(σ) = ∑ r, (∏ j : {j // j ≠ i}, π j (r j)) * ∑ a, π i a * f(e_i.symm (a,r))` |
| `average_update` | None | `A_i f(update σ i a) = A_i f(σ)` |
| `average_preserves_sum` | N | `∑ σ, p(σ)*A_i f(σ) = ∑ σ, p(σ)*f(σ)` |
| `average_const` | N | `A_i (fun _ => c) = (fun _ => c)` |
| `average_commute` | None | `A_i (A_j f) = A_j (A_i f)` |
| `average_sub` | Real weights/functions | `A_i (f-g) = A_i f - A_i g` |
| `squareMass_nonneg` | P | `0 ≤ Q(f)` |
| `average_mul_of_invariant` | `∀ σ a, g(update σ i a) = g(σ)` | `A_i (f*g) = A_i f * g` |
| `average_pythagoras` | N | `D_i(f) = Q(f) - Q(A_i f)` |
| `average_contracts` | P | `Q(A_i f) ≤ Q(f)` |
| `realMean_average` | N | `M(A_i f) = M(f)` |
| `realVariance_eq` | P | `V(f) = Q(f) - M(f)^2` |
| `realVariance_decomposition` | P | `V(f) = D_i(f) + V(A_i f)` |
| `siteEnergy_average_le` | P | `D_j(A_i f) ≤ D_j(f)` |
| `real_tensorization_on` | P; `∀ σ τ, (∀ i ∈ U, σ i = τ i) → f σ = f τ` | `V(f) ≤ ∑ i ∈ U, D_i(f)` |
| `real_tensorization` | P | `V(f) ≤ ∑ i, D_i(f)` |
| `single_fibre_sum` | `R` an additive commutative monoid | `∑ τ, (if AgreeOutside {i} σ τ then g τ else 0) = ∑ a, g(update σ i a)` |
| `conditionalExpectation_product_singleton` | P; complex f | `conditionalExpectation p {i} f σ = A_i^C f(σ)` |
| `average_re` | Complex f | `(A_i^C f(σ)).re = A_i (f.re)(σ)` |
| `average_im` | Complex f | `(A_i^C f(σ)).im = A_i (f.im)(σ)` |
| `variance_re_im` | Complex f | `variance p f = V(f.re) + V(f.im)` |
| `blockDirichlet_re_im` | P; complex f | `blockDirichlet p {i} f = D_i(f.re) + D_i(f.im)` |
| `main` | None outside the frozen statement | `AKLT.Blueprint.Gap.ProductTensorizationStatement` |

## Axiom checks

`Audit.lean` runs `#print axioms` on every exported theorem. All report exactly the permitted three axioms. Complete output:

```text
'AKLT.W.GAP016.productLaw_positiveProbability' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.GAP016.productMass_update' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.GAP016.split_update' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.GAP016.productMass_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.GAP016.sum_productMass_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.GAP016.average_update' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.GAP016.average_preserves_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.GAP016.average_const' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.GAP016.average_commute' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.GAP016.average_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.GAP016.squareMass_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.GAP016.average_mul_of_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.GAP016.average_pythagoras' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.GAP016.average_contracts' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.GAP016.realMean_average' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.GAP016.realVariance_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.GAP016.realVariance_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.GAP016.siteEnergy_average_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.GAP016.real_tensorization_on' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.GAP016.real_tensorization' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.GAP016.single_fibre_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.GAP016.conditionalExpectation_product_singleton' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.GAP016.average_re' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.GAP016.average_im' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.GAP016.variance_re_im' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.GAP016.blockDirichlet_re_im' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.GAP016.main' depends on axioms: [propext, Classical.choice, Quot.sound]
ELAPSED 6.25 s
```

## Build commands and timings

Run from `/home/ubuntu/aklt/wt/LW_GAP016`, with `$HOME/.elan/bin` on `PATH`:

```sh
/usr/bin/time -f 'ELAPSED %e s' lake build AKLT.W.GAP016.Main
/usr/bin/time -f 'ELAPSED %e s' lake env lean AKLT/W/GAP016/Audit.lean
```

- Final main build: success, 18.61 seconds wall time; all four proof modules rebuilt successfully without warnings. Lean reported 4.2–4.5 seconds per module.
- Exact-type and complete axiom audit: success, 6.25 seconds wall time, exit code 0.
- Source scan found no forbidden proof constructs. No frozen statement or file outside this leaf directory was changed.

## Open issues

None. The earlier residual-based `main` has been replaced by an unconditional proof. No residual propositions, unproved dependencies, or cardinality restrictions remain in the delivered proof.

## ORCH-SUMMARY

- STATUS: PROVED.
- Required declaration: `AKLT.W.GAP016.main : AKLT.Blueprint.Gap.ProductTensorizationStatement`.
- Delivered Main.lean, Product.lean, RealTensorization.lean, Conditioning.lean, Audit.lean.
- Exact-type check passed with no additional premise.
- Main build passed; all 27 theorem axiom checks passed.
- Only axioms: propext, Classical.choice, Quot.sound.
- Zero sites and singleton alphabets are included.
- Uses finite-set induction on coordinate dependence in place of an explicit site enumeration.
- Other blueprint leaves are not assumed.
- Open names: none. Limitations: none.
- Orchestrator action: accept the unconditional leaf; no further decision or dependency is needed.
