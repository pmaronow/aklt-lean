STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_GAP017/AKLT/W/GAP017/Main.lean): the exact requested closed theorem.
- [Basic.lean](/home/ubuntu/aklt/wt/LW_GAP017/AKLT/W/GAP017/Basic.lean): conditional expectation is constant on exterior fibres; complex weighted least-squares identity. These two proofs reuse the earlier attempt.
- [Product.lean](/home/ubuntu/aklt/wt/LW_GAP017/AKLT/W/GAP017/Product.lean): normalized product weights, coordinate resampling, identification with the displayed conditional expectation, orthogonal decomposition, contraction, and the required variational minimum.
- [Tensorization.lean](/home/ubuntu/aklt/wt/LW_GAP017/AKLT/W/GAP017/Tensorization.lean): finite commuting coordinate averages and product tensorization, including zero sites.
- [Audit.lean](/home/ubuntu/aklt/wt/LW_GAP017/AKLT/W/GAP017/Audit.lean): exact-type example, declaration signatures, and an axiom audit of every named theorem.
- [audit.log](/home/ubuntu/aklt/reports/LW/GAP017/audit.log), [audit.time](/home/ubuntu/aklt/reports/LW/GAP017/audit.time): successful audit output and timing.

## Exported result

```lean
theorem AKLT.W.GAP017.main : AKLT.Blueprint.Gap.DensityComparisonStatement
```

For the normalized product law `q σ = ∏ x, π x (σ x)` and the statement's positive constants `m`, `M`, the theorem proves both

```lean
∀ f, m * dirichlet q f ≤ dirichlet μ f ∧
  variance μ f ≤ M * variance q f
```

and `PoincareLower μ (m / M)`, under exactly the frozen statement's hypotheses. It has no residual hypotheses.

The lower Dirichlet comparison inserts the conditional mean under `μ` into the product law's one-coordinate variational formula. The variance comparison inserts the constant product mean into the least-squares identity under `μ`. Coordinate averages preserve product expectation, commute, and contract squared weighted norm. Induction over the finite list of sites bounds their total energy loss by the sum of the original coordinate losses; averaging every site gives the constant product mean. Thus `variance q f ≤ dirichlet q f`, and the final comparison loses exactly the single ratio `m / M`.

No other blueprint leaf is imported as a proved lemma or assumed. The only blueprint import is the statement/definition layer through `AKLT.Blueprint.Gap.NodesFinite`.

## Validation

Commands were run from `/home/ubuntu/aklt/wt/LW_GAP017` with `$HOME/.elan/bin` on `PATH`.

| Command | Result | Wall time |
| --- | --- | --- |
| `lake build AKLT.W.GAP017.Main` | Passed; final incremental build rebuilt `Tensorization` (5.6 s) and `Main` (6.3 s), with no warnings | 18.34 s |
| `lake env lean AKLT/W/GAP017/Audit.lean` | Passed, including the exact-type example and all 25 theorem axiom checks | 6.95 s |

The helper modules were also compiled during development. A final source scan found no prohibited constructs and no residual propositions. All 25 named theorems report exactly `[propext, Classical.choice, Quot.sound]`; in particular:

```text
'AKLT.W.GAP017.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## All exported signatures and axiom output

The following is the complete successful `#check` output for the five helper definitions and 25 named theorems, interleaved with `#print axioms` for every theorem:

```text
AKLT.W.GAP017.productWeight {ι : Type} [Fintype ι] {S : ι → Type} (π : (i : ι) → AKLT.Defs.Weight (S i)) :
  AKLT.Defs.Weight (AKLT.Blueprint.Gap.Config S)
AKLT.W.GAP017.average {ι : Type} [DecidableEq ι] {S : ι → Type} [(i : ι) → Fintype (S i)]
  (π : (i : ι) → AKLT.Defs.Weight (S i)) (i : ι) (f : AKLT.Blueprint.Gap.Config S → ℂ) : AKLT.Blueprint.Gap.Config S → ℂ
AKLT.W.GAP017.energy {Ω : Type} [Fintype Ω] (p : AKLT.Defs.Weight Ω) (f : Ω → ℂ) : ℝ
AKLT.W.GAP017.swapLetter {ι : Type} [DecidableEq ι] {S : ι → Type} (i : ι) :
  AKLT.Blueprint.Gap.Config S × S i ≃ AKLT.Blueprint.Gap.Config S × S i
AKLT.W.GAP017.averages {ι : Type} [DecidableEq ι] {S : ι → Type} [(i : ι) → Fintype (S i)]
  (π : (i : ι) → AKLT.Defs.Weight (S i)) : List ι → (AKLT.Blueprint.Gap.Config S → ℂ) → AKLT.Blueprint.Gap.Config S → ℂ
AKLT.W.GAP017.conditionalExpectation_eq_of_agree {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
  [(x : ι) → Fintype (S x)] (p : AKLT.Defs.Weight (AKLT.Blueprint.Gap.Config S)) (U : Finset ι)
  (f : AKLT.Blueprint.Gap.Config S → ℂ) (σ τ : AKLT.Blueprint.Gap.Config S) (hστ : AKLT.Defs.AgreeOutside U σ τ) :
  AKLT.Defs.conditionalExpectation p U f σ = AKLT.Defs.conditionalExpectation p U f τ
'AKLT.W.GAP017.conditionalExpectation_eq_of_agree' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP017.weighted_sq_decomp {Ω : Type} [Fintype Ω] (p : AKLT.Defs.Weight Ω) (hp : AKLT.Defs.Probability p)
  (f : Ω → ℂ) (z : ℂ) :
  ∑ x, p x * Complex.normSq (f x - z) = AKLT.Defs.variance p f + Complex.normSq (AKLT.Defs.complexMean p f - z)
'AKLT.W.GAP017.weighted_sq_decomp' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP017.product_probability {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [(i : ι) → Fintype (S i)]
  (π : (i : ι) → AKLT.Defs.Weight (S i)) (hπ : ∀ (i : ι), AKLT.Defs.PositiveProbability (π i)) :
  AKLT.Defs.PositiveProbability (AKLT.W.GAP017.productWeight π)
'AKLT.W.GAP017.product_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP017.prod_update_factor {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} {R : Type} [CommSemiring R]
  (w : (i : ι) → S i → R) (i : ι) (σ : AKLT.Blueprint.Gap.Config S) (a : S i) :
  ∏ j, w j (Function.update σ i a j) = w i a * ∏ j ∈ Finset.univ.erase i, w j (σ j)
'AKLT.W.GAP017.prod_update_factor' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP017.sum_update {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [(i : ι) → Fintype (S i)] {R : Type}
  [CommSemiring R] (w : (i : ι) → S i → R) (i : ι) (hw : ∑ a, w i a = 1) (f : AKLT.Blueprint.Gap.Config S → R) :
  ∑ σ, (∏ j, w j (σ j)) * ∑ a, w i a * f (Function.update σ i a) = ∑ σ, (∏ j, w j (σ j)) * f σ
'AKLT.W.GAP017.sum_update' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP017.sum_fibre_singleton {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [(i : ι) → Fintype (S i)]
  {R : Type} [AddCommMonoid R] (i : ι) (σ : AKLT.Blueprint.Gap.Config S) (f : AKLT.Blueprint.Gap.Config S → R) :
  (∑ τ, if AKLT.Defs.AgreeOutside {i} σ τ then f τ else 0) = ∑ a, f (Function.update σ i a)
'AKLT.W.GAP017.sum_fibre_singleton' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP017.conditional_product_singleton {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
  [(i : ι) → Fintype (S i)] (π : (i : ι) → AKLT.Defs.Weight (S i)) (hπ : ∀ (i : ι), AKLT.Defs.PositiveProbability (π i))
  (i : ι) (f : AKLT.Blueprint.Gap.Config S → ℂ) :
  AKLT.Defs.conditionalExpectation (AKLT.W.GAP017.productWeight π) {i} f = AKLT.W.GAP017.average π i f
'AKLT.W.GAP017.conditional_product_singleton' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP017.average_update {ι : Type} [DecidableEq ι] {S : ι → Type} [(i : ι) → Fintype (S i)]
  (π : (i : ι) → AKLT.Defs.Weight (S i)) (i : ι) (f : AKLT.Blueprint.Gap.Config S → ℂ) (σ : AKLT.Blueprint.Gap.Config S)
  (a : S i) : AKLT.W.GAP017.average π i f (Function.update σ i a) = AKLT.W.GAP017.average π i f σ
'AKLT.W.GAP017.average_update' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP017.average_sub {ι : Type} [DecidableEq ι] {S : ι → Type} [(i : ι) → Fintype (S i)]
  (π : (i : ι) → AKLT.Defs.Weight (S i)) (i : ι) (f g : AKLT.Blueprint.Gap.Config S → ℂ) :
  (AKLT.W.GAP017.average π i fun σ => f σ - g σ) = fun σ =>
    AKLT.W.GAP017.average π i f σ - AKLT.W.GAP017.average π i g σ
'AKLT.W.GAP017.average_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP017.average_commute {ι : Type} [DecidableEq ι] {S : ι → Type} [(i : ι) → Fintype (S i)]
  (π : (i : ι) → AKLT.Defs.Weight (S i)) (i j : ι) (f : AKLT.Blueprint.Gap.Config S → ℂ) :
  AKLT.W.GAP017.average π i (AKLT.W.GAP017.average π j f) = AKLT.W.GAP017.average π j (AKLT.W.GAP017.average π i f)
'AKLT.W.GAP017.average_commute' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP017.average_idempotent {ι : Type} [DecidableEq ι] {S : ι → Type} [(i : ι) → Fintype (S i)]
  (π : (i : ι) → AKLT.Defs.Weight (S i)) (hπ : ∀ (i : ι), AKLT.Defs.PositiveProbability (π i)) (i : ι)
  (f : AKLT.Blueprint.Gap.Config S → ℂ) :
  AKLT.W.GAP017.average π i (AKLT.W.GAP017.average π i f) = AKLT.W.GAP017.average π i f
'AKLT.W.GAP017.average_idempotent' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP017.sum_product_update {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [(i : ι) → Fintype (S i)]
  (π : (i : ι) → AKLT.Defs.Weight (S i)) (hπ : ∀ (i : ι), AKLT.Defs.PositiveProbability (π i)) (i : ι)
  (f : AKLT.Blueprint.Gap.Config S → ℝ) :
  ∑ σ, AKLT.W.GAP017.productWeight π σ * ∑ a, π i a * f (Function.update σ i a) =
    ∑ σ, AKLT.W.GAP017.productWeight π σ * f σ
'AKLT.W.GAP017.sum_product_update' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP017.mean_average {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [(i : ι) → Fintype (S i)]
  (π : (i : ι) → AKLT.Defs.Weight (S i)) (hπ : ∀ (i : ι), AKLT.Defs.PositiveProbability (π i)) (i : ι)
  (f : AKLT.Blueprint.Gap.Config S → ℂ) :
  AKLT.Defs.complexMean (AKLT.W.GAP017.productWeight π) (AKLT.W.GAP017.average π i f) =
    AKLT.Defs.complexMean (AKLT.W.GAP017.productWeight π) f
'AKLT.W.GAP017.mean_average' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP017.energy_decomp {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [(i : ι) → Fintype (S i)]
  (π : (i : ι) → AKLT.Defs.Weight (S i)) (hπ : ∀ (i : ι), AKLT.Defs.PositiveProbability (π i)) (i : ι)
  (f h : AKLT.Blueprint.Gap.Config S → ℂ) (hh : ∀ (σ : (a : ι) → S a) (a : S i), h (Function.update σ i a) = h σ) :
  (AKLT.W.GAP017.energy (AKLT.W.GAP017.productWeight π) fun σ => f σ - h σ) =
    (AKLT.W.GAP017.energy (AKLT.W.GAP017.productWeight π) fun σ => f σ - AKLT.W.GAP017.average π i f σ) +
      AKLT.W.GAP017.energy (AKLT.W.GAP017.productWeight π) fun σ => AKLT.W.GAP017.average π i f σ - h σ
'AKLT.W.GAP017.energy_decomp' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP017.energy_nonneg {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [(i : ι) → Fintype (S i)]
  (π : (i : ι) → AKLT.Defs.Weight (S i)) (hπ : ∀ (i : ι), AKLT.Defs.PositiveProbability (π i))
  (f : AKLT.Blueprint.Gap.Config S → ℂ) : 0 ≤ AKLT.W.GAP017.energy (AKLT.W.GAP017.productWeight π) f
'AKLT.W.GAP017.energy_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP017.energy_average_le {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [(i : ι) → Fintype (S i)]
  (π : (i : ι) → AKLT.Defs.Weight (S i)) (hπ : ∀ (i : ι), AKLT.Defs.PositiveProbability (π i)) (i : ι)
  (f : AKLT.Blueprint.Gap.Config S → ℂ) :
  AKLT.W.GAP017.energy (AKLT.W.GAP017.productWeight π) (AKLT.W.GAP017.average π i f) ≤
    AKLT.W.GAP017.energy (AKLT.W.GAP017.productWeight π) f
'AKLT.W.GAP017.energy_average_le' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP017.product_singleton_min {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [(i : ι) → Fintype (S i)]
  (π : (i : ι) → AKLT.Defs.Weight (S i)) (hπ : ∀ (i : ι), AKLT.Defs.PositiveProbability (π i)) (i : ι)
  (f h : AKLT.Blueprint.Gap.Config S → ℂ) (hh : ∀ (σ τ : (x : ι) → S x), AKLT.Defs.AgreeOutside {i} σ τ → h σ = h τ) :
  AKLT.Defs.blockDirichlet (AKLT.W.GAP017.productWeight π) {i} f ≤
    ∑ σ, AKLT.W.GAP017.productWeight π σ * Complex.normSq (f σ - h σ)
'AKLT.W.GAP017.product_singleton_min' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP017.mean_averages {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [(i : ι) → Fintype (S i)]
  (π : (i : ι) → AKLT.Defs.Weight (S i)) (hπ : ∀ (i : ι), AKLT.Defs.PositiveProbability (π i)) (l : List ι)
  (f : AKLT.Blueprint.Gap.Config S → ℂ) :
  AKLT.Defs.complexMean (AKLT.W.GAP017.productWeight π) (AKLT.W.GAP017.averages π l f) =
    AKLT.Defs.complexMean (AKLT.W.GAP017.productWeight π) f
'AKLT.W.GAP017.mean_averages' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP017.average_averages {ι : Type} [DecidableEq ι] {S : ι → Type} [(i : ι) → Fintype (S i)]
  (π : (i : ι) → AKLT.Defs.Weight (S i)) (i : ι) (l : List ι) (f : AKLT.Blueprint.Gap.Config S → ℂ) :
  AKLT.W.GAP017.average π i (AKLT.W.GAP017.averages π l f) = AKLT.W.GAP017.averages π l (AKLT.W.GAP017.average π i f)
'AKLT.W.GAP017.average_averages' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP017.averages_fixed {ι : Type} [DecidableEq ι] {S : ι → Type} [(i : ι) → Fintype (S i)]
  (π : (i : ι) → AKLT.Defs.Weight (S i)) (hπ : ∀ (i : ι), AKLT.Defs.PositiveProbability (π i)) (i : ι) (l : List ι)
  (hi : i ∈ l) (f : AKLT.Blueprint.Gap.Config S → ℂ) :
  AKLT.W.GAP017.average π i (AKLT.W.GAP017.averages π l f) = AKLT.W.GAP017.averages π l f
'AKLT.W.GAP017.averages_fixed' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP017.energy_averages_bound {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [(i : ι) → Fintype (S i)]
  (π : (i : ι) → AKLT.Defs.Weight (S i)) (hπ : ∀ (i : ι), AKLT.Defs.PositiveProbability (π i)) (l : List ι)
  (f : AKLT.Blueprint.Gap.Config S → ℂ) :
  AKLT.W.GAP017.energy (AKLT.W.GAP017.productWeight π) f -
      AKLT.W.GAP017.energy (AKLT.W.GAP017.productWeight π) (AKLT.W.GAP017.averages π l f) ≤
    (List.map
        (fun i => AKLT.W.GAP017.energy (AKLT.W.GAP017.productWeight π) fun σ => f σ - AKLT.W.GAP017.average π i f σ)
        l).sum
'AKLT.W.GAP017.energy_averages_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP017.constant_of_updates {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
  (g : AKLT.Blueprint.Gap.Config S → ℂ) (hg : ∀ (i : ι) (σ : (a : ι) → S a) (a : S i), g (Function.update σ i a) = g σ)
  (σ τ : AKLT.Blueprint.Gap.Config S) : g σ = g τ
'AKLT.W.GAP017.constant_of_updates' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP017.averages_all {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [(i : ι) → Fintype (S i)]
  (π : (i : ι) → AKLT.Defs.Weight (S i)) (hπ : ∀ (i : ι), AKLT.Defs.PositiveProbability (π i)) (l : List ι)
  (hl : ∀ (i : ι), i ∈ l) (f : AKLT.Blueprint.Gap.Config S → ℂ) :
  AKLT.W.GAP017.averages π l f = fun x => AKLT.Defs.complexMean (AKLT.W.GAP017.productWeight π) f
'AKLT.W.GAP017.averages_all' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP017.product_tensorization {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [(i : ι) → Fintype (S i)]
  (π : (i : ι) → AKLT.Defs.Weight (S i)) (hπ : ∀ (i : ι), AKLT.Defs.PositiveProbability (π i)) :
  AKLT.Defs.PoincareLower (AKLT.W.GAP017.productWeight π) 1
'AKLT.W.GAP017.product_tensorization' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP017.main : AKLT.Blueprint.Gap.DensityComparisonStatement
'AKLT.W.GAP017.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Open issues

None. The earlier residual-based `main_from_residuals` has been replaced by the unconditional requested `main`. No existing statement or library file was edited, and no additional premise or change of conclusion was needed.

## ORCH-SUMMARY

- STATUS: PROVED.
- Delivered `AKLT.W.GAP017.main : AKLT.Blueprint.Gap.DensityComparisonStatement` in `AKLT/W/GAP017/Main.lean`.
- Helpers: `Basic.lean`, `Product.lean`, and `Tensorization.lean`; verification: `Audit.lean`.
- Product reference is normalized; both density constants are positive; the conclusion uses one ratio `m / M`.
- Tensorization covers complex functions, dependent finite alphabets, and the zero-site case.
- Exact-type example and final target build pass.
- Every named theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.
- No residual assumptions, other leaf dependencies, extra premises, limitations, or statement deviations.
- Open names: none. No orchestrator decision is required.
