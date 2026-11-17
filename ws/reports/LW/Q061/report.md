STATUS: PROVED

## Files

All Lean files are under `/home/ubuntu/aklt/wt/LW_Q061/AKLT/W/Q061/`:

- [Main.lean](/home/ubuntu/aklt/wt/LW_Q061/AKLT/W/Q061/Main.lean): the requested closed theorem and the Dirichlet identity.
- [Product.lean](/home/ubuntu/aklt/wt/LW_Q061/AKLT/W/Q061/Product.lean): product weights, coordinate averages, stationarity, orthogonality, and the explicit singleton-fibre calculation.
- [Projections.lean](/home/ubuntu/aklt/wt/LW_Q061/AKLT/W/Q061/Projections.lean): tensorization for finite lists of commuting projections.
- [Tensorization.lean](/home/ubuntu/aklt/wt/LW_Q061/AKLT/W/Q061/Tensorization.lean): full averaging equals the mean; complex Efron–Stein.
- [Audit.lean](/home/ubuntu/aklt/wt/LW_Q061/AKLT/W/Q061/Audit.lean): independent exact-type check, declaration signatures, and axiom checks for all 27 named theorems.

The earlier report is preserved as `report.luna.md`. Final command logs are [build.log](/home/ubuntu/aklt/reports/LW/Q061/build.log) and [audit.log](/home/ubuntu/aklt/reports/LW/Q061/audit.log).

## Result and proof

```lean
theorem AKLT.W.Q061.main : AKLT.Blueprint.Q.ProductPoincareStatement
```

This theorem has no residual premises. Both obligations from the earlier attempt are now proved: `product_tensorization` proves Efron–Stein, and `conditionalExpectation_singleton` together with `product_dirichlet` identifies the frozen Dirichlet form.

The proof follows Appendix A's commuting-projection argument. Write π for `productMass p`, Eₓ for `siteAverage p x`, and Q(f) for `energy p f = ∑ σ, π σ * Complex.normSq (f σ)`. Swapping the old coordinate with a fresh letter proves that Eₓ preserves the product mean. Factoring out functions independent of that coordinate gives orthogonality and Q(f) = Q(f − Eₓf) + Q(Eₓf), hence contraction. The coordinate averages commute. Induction on a finite list of averages bounds the lost energy by the sum of the original single-site energies. Averaging every coordinate gives the constant mean. Apply the bound to the centered function and then use the explicit singleton-fibre identity.

The proof handles complex functions directly. Empty site sets and singleton alphabets require no extra premises or separate exceptions. Positivity of the exterior product justifies the fibre cancellation. Every site has coefficient one; there is no volume normalization. Only the frozen definitions and Mathlib are used, with no dependency on another blueprint leaf.

## Exported declarations and statements

There are five helper definitions and 27 named theorems, all in `AKLT.W.Q061`. `resampleSwap x` sends `(σ, a)` to `(Function.update σ x a, σ x)`; `averageList` applies the listed coordinate maps successively. The complete Lean-printed signatures follow.

```text
AKLT.W.Q061.productMass.{u_1, u_2} {ι : Type u_1} [Fintype ι] {S : ι → Type u_2} (p : (x : ι) → AKLT.Defs.Weight (S x))
  (σ : (x : ι) → S x) : ℝ
AKLT.W.Q061.siteAverage.{u_1, u_2} {ι : Type u_1} [DecidableEq ι] {S : ι → Type u_2} [(x : ι) → Fintype (S x)]
  (p : (x : ι) → AKLT.Defs.Weight (S x)) (x : ι) (f : ((x : ι) → S x) → ℂ) (σ : (x : ι) → S x) : ℂ
AKLT.W.Q061.energy.{u_1, u_2} {ι : Type u_1} [Fintype ι] [DecidableEq ι] {S : ι → Type u_2} [(x : ι) → Fintype (S x)]
  (p : (x : ι) → AKLT.Defs.Weight (S x)) (f : ((x : ι) → S x) → ℂ) : ℝ
AKLT.W.Q061.productMass_sum.{u_1, u_2} {ι : Type u_1} [Fintype ι] [DecidableEq ι] {S : ι → Type u_2}
  [(x : ι) → Fintype (S x)] (p : (x : ι) → AKLT.Defs.Weight (S x))
  (hp : ∀ (x : ι), AKLT.Defs.PositiveProbability (p x)) : ∑ σ, AKLT.W.Q061.productMass p σ = 1
AKLT.W.Q061.productMass_pos.{u_1, u_2} {ι : Type u_1} [Fintype ι] {S : ι → Type u_2} [(x : ι) → Fintype (S x)]
  (p : (x : ι) → AKLT.Defs.Weight (S x)) (hp : ∀ (x : ι), AKLT.Defs.PositiveProbability (p x)) (σ : (x : ι) → S x) :
  0 < AKLT.W.Q061.productMass p σ
AKLT.W.Q061.energy_nonneg.{u_1, u_2} {ι : Type u_1} [Fintype ι] [DecidableEq ι] {S : ι → Type u_2}
  [(x : ι) → Fintype (S x)] (p : (x : ι) → AKLT.Defs.Weight (S x)) (hp : ∀ (x : ι), AKLT.Defs.PositiveProbability (p x))
  (f : ((x : ι) → S x) → ℂ) : 0 ≤ AKLT.W.Q061.energy p f
AKLT.W.Q061.productMass_update.{u_1, u_2} {ι : Type u_1} [Fintype ι] [DecidableEq ι] {S : ι → Type u_2}
  (p : (x : ι) → AKLT.Defs.Weight (S x)) (x : ι) (σ : (x : ι) → S x) (a : S x) :
  AKLT.W.Q061.productMass p (Function.update σ x a) = (∏ y ∈ Finset.univ.erase x, p y (σ y)) * p x a
AKLT.W.Q061.productMass_balance.{u_1, u_2} {ι : Type u_1} [Fintype ι] [DecidableEq ι] {S : ι → Type u_2}
  (p : (x : ι) → AKLT.Defs.Weight (S x)) (x : ι) (σ : (x : ι) → S x) (a : S x) :
  AKLT.W.Q061.productMass p σ * p x a = AKLT.W.Q061.productMass p (Function.update σ x a) * p x (σ x)
AKLT.W.Q061.resampleSwap.{u_1, u_2} {ι : Type u_1} [DecidableEq ι] {S : ι → Type u_2} (x : ι) :
  ((x : ι) → S x) × S x ≃ ((x : ι) → S x) × S x
AKLT.W.Q061.mean_siteAverage.{u_1, u_2} {ι : Type u_1} [Fintype ι] [DecidableEq ι] {S : ι → Type u_2}
  [(x : ι) → Fintype (S x)] (p : (x : ι) → AKLT.Defs.Weight (S x)) (hp : ∀ (x : ι), AKLT.Defs.PositiveProbability (p x))
  (x : ι) (f : ((x : ι) → S x) → ℂ) :
  AKLT.Defs.complexMean (AKLT.W.Q061.productMass p) (AKLT.W.Q061.siteAverage p x f) =
    AKLT.Defs.complexMean (AKLT.W.Q061.productMass p) f
AKLT.W.Q061.siteAverage_update.{u_1, u_2} {ι : Type u_1} [DecidableEq ι] {S : ι → Type u_2} [(x : ι) → Fintype (S x)]
  (p : (x : ι) → AKLT.Defs.Weight (S x)) (x : ι) (f : ((x : ι) → S x) → ℂ) (σ : (x : ι) → S x) (a : S x) :
  AKLT.W.Q061.siteAverage p x f (Function.update σ x a) = AKLT.W.Q061.siteAverage p x f σ
AKLT.W.Q061.siteAverage_sub.{u_1, u_2} {ι : Type u_1} [DecidableEq ι] {S : ι → Type u_2} [(x : ι) → Fintype (S x)]
  (p : (x : ι) → AKLT.Defs.Weight (S x)) (x : ι) (f g : ((x : ι) → S x) → ℂ) :
  AKLT.W.Q061.siteAverage p x (f - g) = AKLT.W.Q061.siteAverage p x f - AKLT.W.Q061.siteAverage p x g
AKLT.W.Q061.siteAverage_idem.{u_1, u_2} {ι : Type u_1} [DecidableEq ι] {S : ι → Type u_2} [(x : ι) → Fintype (S x)]
  (p : (x : ι) → AKLT.Defs.Weight (S x)) (hp : ∀ (x : ι), AKLT.Defs.PositiveProbability (p x)) (x : ι)
  (f : ((x : ι) → S x) → ℂ) :
  AKLT.W.Q061.siteAverage p x (AKLT.W.Q061.siteAverage p x f) = AKLT.W.Q061.siteAverage p x f
AKLT.W.Q061.siteAverage_commute.{u_1, u_2} {ι : Type u_1} [DecidableEq ι] {S : ι → Type u_2} [(x : ι) → Fintype (S x)]
  (p : (x : ι) → AKLT.Defs.Weight (S x)) (x y : ι) (f : ((x : ι) → S x) → ℂ) :
  AKLT.W.Q061.siteAverage p x (AKLT.W.Q061.siteAverage p y f) =
    AKLT.W.Q061.siteAverage p y (AKLT.W.Q061.siteAverage p x f)
AKLT.W.Q061.siteAverage_const.{u_1, u_2} {ι : Type u_1} [DecidableEq ι] {S : ι → Type u_2} [(x : ι) → Fintype (S x)]
  (p : (x : ι) → AKLT.Defs.Weight (S x)) (hp : ∀ (x : ι), AKLT.Defs.PositiveProbability (p x)) (x : ι) (c : ℂ) :
  (AKLT.W.Q061.siteAverage p x fun x => c) = fun x => c
AKLT.W.Q061.mean_const.{u_1, u_2} {ι : Type u_1} [Fintype ι] [DecidableEq ι] {S : ι → Type u_2}
  [(x : ι) → Fintype (S x)] (p : (x : ι) → AKLT.Defs.Weight (S x)) (hp : ∀ (x : ι), AKLT.Defs.PositiveProbability (p x))
  (c : ℂ) : (AKLT.Defs.complexMean (AKLT.W.Q061.productMass p) fun x => c) = c
AKLT.W.Q061.mean_sub.{u_1, u_2} {ι : Type u_1} [Fintype ι] [DecidableEq ι] {S : ι → Type u_2} [(x : ι) → Fintype (S x)]
  (w : AKLT.Defs.Weight ((x : ι) → S x)) (f g : ((x : ι) → S x) → ℂ) :
  AKLT.Defs.complexMean w (f - g) = AKLT.Defs.complexMean w f - AKLT.Defs.complexMean w g
AKLT.W.Q061.siteAverage_mul_fixed.{u_1, u_2} {ι : Type u_1} [DecidableEq ι] {S : ι → Type u_2} [(x : ι) → Fintype (S x)]
  (p : (x : ι) → AKLT.Defs.Weight (S x)) (x : ι) (f g : ((x : ι) → S x) → ℂ)
  (hg : ∀ (σ : (a : ι) → S a) (a : S x), g (Function.update σ x a) = g σ) :
  AKLT.W.Q061.siteAverage p x (f * g) = AKLT.W.Q061.siteAverage p x f * g
AKLT.W.Q061.mean_cross_zero.{u_1, u_2} {ι : Type u_1} [Fintype ι] [DecidableEq ι] {S : ι → Type u_2}
  [(x : ι) → Fintype (S x)] (p : (x : ι) → AKLT.Defs.Weight (S x)) (hp : ∀ (x : ι), AKLT.Defs.PositiveProbability (p x))
  (x : ι) (f : ((x : ι) → S x) → ℂ) :
  (AKLT.Defs.complexMean (AKLT.W.Q061.productMass p) fun σ =>
      (f σ - AKLT.W.Q061.siteAverage p x f σ) * star (AKLT.W.Q061.siteAverage p x f σ)) =
    0
AKLT.W.Q061.energy_split.{u_1, u_2} {ι : Type u_1} [Fintype ι] [DecidableEq ι] {S : ι → Type u_2}
  [(x : ι) → Fintype (S x)] (p : (x : ι) → AKLT.Defs.Weight (S x)) (hp : ∀ (x : ι), AKLT.Defs.PositiveProbability (p x))
  (x : ι) (f : ((x : ι) → S x) → ℂ) :
  AKLT.W.Q061.energy p f =
    AKLT.W.Q061.energy p (f - AKLT.W.Q061.siteAverage p x f) + AKLT.W.Q061.energy p (AKLT.W.Q061.siteAverage p x f)
AKLT.W.Q061.sum_fibre.{u_1, u_2, u_3} {ι : Type u_1} [Fintype ι] [DecidableEq ι] {S : ι → Type u_2}
  [(x : ι) → Fintype (S x)] {M : Type u_3} [AddCommMonoid M] (x : ι) (σ : (x : ι) → S x) (F : ((x : ι) → S x) → M) :
  (∑ τ, if AKLT.Defs.AgreeOutside {x} σ τ then F τ else 0) = ∑ a, F (Function.update σ x a)
AKLT.W.Q061.conditionalExpectation_singleton.{u_1, u_2} {ι : Type u_1} [Fintype ι] [DecidableEq ι] {S : ι → Type u_2}
  [(x : ι) → Fintype (S x)] (p : (x : ι) → AKLT.Defs.Weight (S x)) (hp : ∀ (x : ι), AKLT.Defs.PositiveProbability (p x))
  (x : ι) (f : ((x : ι) → S x) → ℂ) (σ : (x : ι) → S x) :
  AKLT.Defs.conditionalExpectation (AKLT.W.Q061.productMass p) {x} f σ = AKLT.W.Q061.siteAverage p x f σ
AKLT.W.Q061.averageList.{u_1, u_2} {I : Type u_1} {F : Type u_2} (E : I → F → F) : List I → F → F
AKLT.W.Q061.averageList_commute.{u_1, u_2} {I : Type u_1} {F : Type u_2} (E : I → F → F)
  (hc : ∀ (x y : I) (f : F), E x (E y f) = E y (E x f)) (x : I) (l : List I) (f : F) :
  E x (AKLT.W.Q061.averageList E l f) = AKLT.W.Q061.averageList E l (E x f)
AKLT.W.Q061.averageList_fixed.{u_1, u_2} {I : Type u_1} {F : Type u_2} (E : I → F → F)
  (hc : ∀ (x y : I) (f : F), E x (E y f) = E y (E x f)) (hi : ∀ (x : I) (f : F), E x (E x f) = E x f) (x : I)
  (l : List I) (hx : x ∈ l) (f : F) : E x (AKLT.W.Q061.averageList E l f) = AKLT.W.Q061.averageList E l f
AKLT.W.Q061.projection_tensorization.{u_1, u_2} {I : Type u_1} {F : Type u_2} [AddCommGroup F] (E : I → F → F)
  (q : F → ℝ) (hq : ∀ (f : F), 0 ≤ q f) (hp : ∀ (x : I) (f : F), q f = q (f - E x f) + q (E x f))
  (hc : ∀ (x y : I) (f : F), E x (E y f) = E y (E x f)) (hs : ∀ (x : I) (f g : F), E x (f - g) = E x f - E x g)
  (l : List I) (f : F) : q f ≤ q (AKLT.W.Q061.averageList E l f) + (List.map (fun x => q (f - E x f)) l).sum
AKLT.W.Q061.constant_of_update_invariant.{u_1, u_2} {ι : Type u_1} [Fintype ι] [DecidableEq ι] {S : ι → Type u_2}
  (g : ((x : ι) → S x) → ℂ) (hg : ∀ (x : ι) (σ : (a : ι) → S a) (a : S x), g (Function.update σ x a) = g σ)
  (σ τ : (x : ι) → S x) : g σ = g τ
AKLT.W.Q061.mean_averageList.{u_1, u_2} {ι : Type u_1} [Fintype ι] [DecidableEq ι] {S : ι → Type u_2}
  [(x : ι) → Fintype (S x)] (p : (x : ι) → AKLT.Defs.Weight (S x)) (hp : ∀ (x : ι), AKLT.Defs.PositiveProbability (p x))
  (l : List ι) (f : ((x : ι) → S x) → ℂ) :
  AKLT.Defs.complexMean (AKLT.W.Q061.productMass p) (AKLT.W.Q061.averageList (AKLT.W.Q061.siteAverage p) l f) =
    AKLT.Defs.complexMean (AKLT.W.Q061.productMass p) f
AKLT.W.Q061.averageList_univ.{u_1, u_2} {ι : Type u_1} [Fintype ι] [DecidableEq ι] {S : ι → Type u_2}
  [(x : ι) → Fintype (S x)] (p : (x : ι) → AKLT.Defs.Weight (S x)) (hp : ∀ (x : ι), AKLT.Defs.PositiveProbability (p x))
  (f : ((x : ι) → S x) → ℂ) :
  AKLT.W.Q061.averageList (AKLT.W.Q061.siteAverage p) Finset.univ.toList f = fun x =>
    AKLT.Defs.complexMean (AKLT.W.Q061.productMass p) f
AKLT.W.Q061.product_tensorization.{u_1, u_2} {ι : Type u_1} [Fintype ι] [DecidableEq ι] {S : ι → Type u_2}
  [(x : ι) → Fintype (S x)] (p : (x : ι) → AKLT.Defs.Weight (S x)) (hp : ∀ (x : ι), AKLT.Defs.PositiveProbability (p x))
  (f : ((x : ι) → S x) → ℂ) :
  AKLT.Defs.variance (AKLT.W.Q061.productMass p) f ≤ ∑ x, AKLT.W.Q061.energy p (f - AKLT.W.Q061.siteAverage p x f)
AKLT.W.Q061.product_dirichlet.{u_1, u_2} {ι : Type u_1} [Fintype ι] [DecidableEq ι] {S : ι → Type u_2}
  [(x : ι) → Fintype (S x)] (p : (x : ι) → AKLT.Defs.Weight (S x)) (hp : ∀ (x : ι), AKLT.Defs.PositiveProbability (p x))
  (f : ((x : ι) → S x) → ℂ) :
  AKLT.Defs.dirichlet (AKLT.W.Q061.productMass p) f = ∑ x, AKLT.W.Q061.energy p (f - AKLT.W.Q061.siteAverage p x f)
AKLT.W.Q061.main : AKLT.Blueprint.Q.ProductPoincareStatement
```

## Axiom audit

`Audit.lean` runs `#print axioms` on every named theorem. All dependencies are among `propext`, `Classical.choice`, and `Quot.sound`; no residual or additional axiom occurs. Exact output:

```text
'AKLT.W.Q061.productMass_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q061.productMass_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q061.energy_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q061.productMass_update' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q061.productMass_balance' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q061.mean_siteAverage' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q061.siteAverage_update' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q061.siteAverage_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q061.siteAverage_idem' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q061.siteAverage_commute' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q061.siteAverage_const' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q061.mean_const' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q061.mean_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q061.siteAverage_mul_fixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q061.mean_cross_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q061.energy_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q061.sum_fibre' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q061.conditionalExpectation_singleton' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q061.averageList_commute' does not depend on any axioms
'AKLT.W.Q061.averageList_fixed' depends on axioms: [propext]
'AKLT.W.Q061.projection_tensorization' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q061.constant_of_update_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q061.mean_averageList' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q061.averageList_univ' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q061.product_tensorization' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q061.product_dirichlet' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q061.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build and exact-type validation

Commands ran with `PATH="$HOME/.elan/bin:$PATH"`:

- `lake build AKLT.W.Q061.Main` — succeeded without warnings; 19.75 seconds wall time. Newly rebuilt modules: Product 5.8 s, Tensorization 5.0 s, Main 3.8 s; Projections was already built.
- `lake env lean AKLT/W/Q061/Audit.lean` — succeeded; 5.46 seconds wall time. It independently checks `example : AKLT.Blueprint.Q.ProductPoincareStatement := AKLT.W.Q061.main` and audits all exported named theorems.

A source scan found none of the forbidden proof constructs. No frozen statement or existing file outside Q061 was changed.

## Open issues

None. The earlier `ProductTensorizationResidual` and `ProductBlockIdentityResidual` premises have been removed.

## ORCH-SUMMARY

- STATUS: PROVED.
- Delivered `AKLT.W.Q061.main : AKLT.Blueprint.Q.ProductPoincareStatement`, with no additional premises.
- Source files: Main.lean, Product.lean, Projections.lean, Tensorization.lean, Audit.lean under AKLT/W/Q061/.
- Method: complex weighted orthogonality and finite commuting-projection tensorization, as in Appendix A.
- Singleton conditional expectation is proved equal to the explicit marginal average.
- Empty site sets and singleton alphabets are included; rate is one per site, without volume normalization.
- Main build and independent exact-type audit both pass.
- All 27 named theorem axiom checks use only the permitted standard axioms (or a subset).
- No other blueprint leaf is assumed; no residuals remain.
- Open names: none. Limitations: none. Required-scope deviations: none.
- Orchestrator can accept this leaf; no further decision or handoff is needed.
