STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_GAP017/AKLT/W/GAP017/Main.lean)

## Delivered declarations

```lean
theorem AKLT.W.GAP017.conditionalExpectation_eq_of_agree
    {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
    [∀ x, Fintype (S x)] (p : Weight (Config S)) (U : Finset ι)
    (f : Config S → ℂ) (σ τ : Config S) (h : AgreeOutside U σ τ) :
    conditionalExpectation p U f σ = conditionalExpectation p U f τ

theorem AKLT.W.GAP017.weighted_sq_decomp
    {Ω : Type} [Fintype Ω] (p : Weight Ω) (hp : Probability p)
    (f : Ω → ℂ) (z : ℂ) :
    (∑ x, p x * Complex.normSq (f x - z)) =
      variance p f + Complex.normSq (complexMean p f - z)

def AKLT.W.GAP017.Residual_ConditionalVarianceVariational : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : ι → Type)
    [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (p : Weight (Config S)), PositiveProbability p → ∀ U (f h : Config S → ℂ),
      (∀ σ τ, AgreeOutside U σ τ → h σ = h τ) →
      blockDirichlet p U f ≤ ∑ σ, p σ * Complex.normSq (f σ - h σ)

def AKLT.W.GAP017.Residual_ProductTensorization : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : ι → Type)
    [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (π : (x : ι) → Weight (S x)), (∀ x, PositiveProbability (π x)) →
    PoincareLower (fun σ => ∏ x, π x (σ x)) 1

theorem AKLT.W.GAP017.main_from_residuals
    (hVariational : AKLT.W.GAP017.Residual_ConditionalVarianceVariational)
    (hTensor : AKLT.W.GAP017.Residual_ProductTensorization) :
    AKLT.Blueprint.Gap.DensityComparisonStatement
```

`main_from_residuals` proves both requested density comparisons from the variational residual and combines them with product tensorization to obtain the single ratio `m / M`.

The requested declaration `AKLT.W.GAP017.main : AKLT.Blueprint.Gap.DensityComparisonStatement` is not yet proved. The two residual propositions are closed and each is a strict subproblem of the leaf; no unproved fact is hidden as an axiom.

## Axioms

`#print axioms` for each exported theorem (`conditionalExpectation_eq_of_agree`, `weighted_sq_decomp`, and `main_from_residuals`) returned:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.GAP017.Main` — succeeded, 8.8 s for the module (18.6 s wall time including Lake startup).
- A separate `lake env lean /tmp/GAP017_Audit.lean` axiom audit succeeded.

## Open issues

- `AKLT.W.GAP017.Residual_ConditionalVarianceVariational` remains unproved. The missing step is the finite fibre regrouping/orthogonality argument that establishes the conditional mean as the minimizer on each exterior fibre.
- `AKLT.W.GAP017.Residual_ProductTensorization` remains unproved. The missing step is the finite commuting-coordinate projection (or equivalent product variance) argument.
- Because these residuals remain, the exact requested declaration `AKLT.W.GAP017.main` is not delivered.

## ORCH-SUMMARY

- Delivered a compiled `main_from_residuals` deriving the leaf from two explicit closed residual propositions.
- Proved the finite complex least-squares identity and invariance of conditional expectation across an exterior fibre.
- Open exact declarations: `AKLT.W.GAP017.Residual_ConditionalVarianceVariational`, `AKLT.W.GAP017.Residual_ProductTensorization`, and requested `AKLT.W.GAP017.main`.
- No axioms beyond `propext`, `Classical.choice`, and `Quot.sound` appear in the checked theorems.
- Module build succeeded; full leaf proof remains incomplete.
