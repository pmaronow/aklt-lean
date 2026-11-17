STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_GAP014/AKLT/W/GAP014/Main.lean): the requested signed-frame theorem, using the earlier attempt's interaction bounds and normalization proof.
- [FiniteVariance.lean](/home/ubuntu/aklt/wt/LW_GAP014/AKLT/W/GAP014/FiniteVariance.lean): finite complex least squares, conditional orthogonal decomposition, and the one-ratio density comparison.
- [Product.lean](/home/ubuntu/aklt/wt/LW_GAP014/AKLT/W/GAP014/Product.lean): product normalization, explicit coordinate conditional expectations, commuting averages, and rate-one tensorization.
- [Audit.lean](/home/ubuntu/aklt/wt/LW_GAP014/AKLT/W/GAP014/Audit.lean): exact-type check and axiom checks for every exported theorem.
- [audit.log](/home/ubuntu/aklt/reports/LW/GAP014/audit.log) and [audit.time](/home/ubuntu/aklt/reports/LW/GAP014/audit.time): compiler output and measured audit duration.

## Delivered theorem

```lean
theorem AKLT.W.GAP014.main :
    AKLT.Blueprint.Gap.SignedFrameBlockStatement
```

This theorem is unconditional as a proof of the frozen closed proposition. It has no residual hypotheses. The earlier `ProductTensorizationResidual`, `BoundedDensityComparisonResidual`, and `main_from_residuals` declarations have been replaced by proved finite-sum results and `main`.

## Proof

Normalize each strictly positive site weight to a probability `π x`. Their product `q` is a strictly positive probability. Both branches of each signed edge factor satisfy the supplied lower and upper bounds, so the interaction `ψ` lies between `lo = frameBound ^ E.card` and `hi = (2-frameBound) ^ E.card`. All partition sums and site normalizers are positive, and the normalized raw weight equals `q σ * ψ σ / Z`, where `Z = expectation q ψ`.

The two missing analytic steps are proved locally. Complex least squares is established by real and imaginary square expansions. Fibre normalization and detailed balance give stationarity of conditional averaging, the conditional variational bound, its norm contraction, and the variance decomposition. For a product probability, each singleton conditional average is explicitly the one-coordinate weighted sum; different coordinate averages commute. Induction on the finite set of coordinates on which a function depends proves tensorization, with the empty set handled by constant functions.

For `m*q ≤ μ ≤ M*q`, conditional minimization gives `m * dirichlet q f ≤ dirichlet μ f`, while constant minimization gives `variance μ f ≤ M * variance q f`. Tensorization therefore yields `PoincareLower μ (m/M)`. Taking `m = lo/Z` and `M = hi/Z` cancels `Z` and gives `frameRatio ^ E.card`.

Every supplied edge is checked for proper colouring. Both signs are covered independently. All fixed boundary factors remain within the strictly positive site weights and contribute no extra exponent. Empty site sets and empty interaction products are covered. The proof uses no other blueprint leaf as a lemma and makes no arbitrary-unit-pin positivity assertion.

## Exported declarations and axioms

The public definition `AKLT.W.GAP014.productWeight` is the product weight on the finite dependent configuration space, with defining equation `productWeight π σ = ∏ i, π i (σ i)`.

The following is the complete successful `#check` and `#print axioms` output for the seven exported theorems. Other supporting lemmas and auxiliary definitions are private.

```text
AKLT.W.GAP014.main : AKLT.Blueprint.Gap.SignedFrameBlockStatement
AKLT.W.GAP014.ce_sub {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [(i : ι) → Fintype (S i)]
  (p : AKLT.Defs.Weight (AKLT.Blueprint.Gap.Config S)) (U : Finset ι) (f g : AKLT.Blueprint.Gap.Config S → ℂ) :
  (AKLT.Defs.conditionalExpectation p U fun σ => f σ - g σ) = fun σ =>
    AKLT.Defs.conditionalExpectation p U f σ - AKLT.Defs.conditionalExpectation p U g σ
AKLT.W.GAP014.ce_energy_le {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [(i : ι) → Fintype (S i)]
  (p : AKLT.Defs.Weight (AKLT.Blueprint.Gap.Config S)) (hp : ∀ (σ : AKLT.Blueprint.Gap.Config S), 0 < p σ)
  (U : Finset ι) (f : AKLT.Blueprint.Gap.Config S → ℂ) :
  ∑ σ, p σ * Complex.normSq (AKLT.Defs.conditionalExpectation p U f σ) ≤ ∑ σ, p σ * Complex.normSq (f σ)
AKLT.W.GAP014.ce_variance_identity {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [(i : ι) → Fintype (S i)]
  (p : AKLT.Defs.Weight (AKLT.Blueprint.Gap.Config S)) (hp : ∀ (σ : AKLT.Blueprint.Gap.Config S), 0 < p σ)
  (U : Finset ι) (f : AKLT.Blueprint.Gap.Config S → ℂ) :
  AKLT.Defs.variance p f =
    AKLT.Defs.blockDirichlet p U f + AKLT.Defs.variance p (AKLT.Defs.conditionalExpectation p U f)
AKLT.W.GAP014.density_comparison {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [(i : ι) → Fintype (S i)]
  (q μ : AKLT.Defs.Weight (AKLT.Blueprint.Gap.Config S)) (hq : AKLT.Defs.PositiveProbability q)
  (hμ : AKLT.Defs.PositiveProbability μ) (hgap : AKLT.Defs.PoincareLower q 1) (m M : ℝ) (hm : 0 < m) (hM : 0 < M)
  (hbound : ∀ (σ : AKLT.Blueprint.Gap.Config S), m * q σ ≤ μ σ ∧ μ σ ≤ M * q σ) : AKLT.Defs.PoincareLower μ (m / M)
AKLT.W.GAP014.productWeight_probability {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [(i : ι) → Fintype (S i)]
  (π : (i : ι) → AKLT.Defs.Weight (S i)) (hπ : ∀ (i : ι), AKLT.Defs.PositiveProbability (π i)) :
  AKLT.Defs.PositiveProbability (AKLT.W.GAP014.productWeight π)
AKLT.W.GAP014.product_gap {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [(i : ι) → Fintype (S i)]
  (π : (i : ι) → AKLT.Defs.Weight (S i)) (hπ : ∀ (i : ι), AKLT.Defs.PositiveProbability (π i)) :
  AKLT.Defs.PoincareLower (AKLT.W.GAP014.productWeight π) 1
'AKLT.W.GAP014.ce_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.GAP014.ce_energy_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.GAP014.ce_variance_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.GAP014.density_comparison' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.GAP014.productWeight_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.GAP014.product_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.GAP014.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Validation

Commands ran from `/home/ubuntu/aklt/wt/LW_GAP014` with `$HOME/.elan/bin` on `PATH`.

- `lake build AKLT.W.GAP014.Main` — passed. Lake reported compilation times of 7.0 seconds for `FiniteVariance`, 5.9 seconds for `Product`, and 8.8 seconds for `Main`. The final successful build emitted no warnings or errors.
- `lake env lean AKLT/W/GAP014/Audit.lean` — passed, exit status 0, 6.84 seconds wall time measured with `/usr/bin/time`. This checks the exact requested type through an import of `Main` and audits every exported theorem.
- Source scan found no forbidden proof placeholders, extra axioms, or prohibited mechanisms. All exported theorem axiom sets are exactly `[propext, Classical.choice, Quot.sound]`.
- `git diff --name-only` is empty: no tracked existing files were changed. All delivered Lean sources are in `AKLT/W/GAP014/`.

## Open issues

None. No residual statements or extra premises remain.

## ORCH-SUMMARY

- STATUS: PROVED.
- Exact deliverable: `AKLT.W.GAP014.main : AKLT.Blueprint.Gap.SignedFrameBlockStatement`.
- Files: `Main.lean`, `FiniteVariance.lean`, `Product.lean`, `Audit.lean`, all under `AKLT/W/GAP014/`.
- Reused the prior signed-edge and normalization argument; proved both former residuals locally.
- Product tensorization and one-ratio density comparison are proved from finite sums.
- Both interaction signs, arbitrary finite blocks, and empty products are covered.
- Site weights contain all fixed boundary factors; only `E.card` enters the exponent.
- No other blueprint leaf is imported as a proved dependency.
- `lake build AKLT.W.GAP014.Main` passed with no warnings or errors.
- Exact-type and all exported-theorem axiom checks passed in `Audit.lean`.
- Allowed axioms only: `propext`, `Classical.choice`, `Quot.sound`.
- Open declarations: none. Limitations or deviations: none.
- Orchestrator action: accept the exact theorem and include its local helper modules.
