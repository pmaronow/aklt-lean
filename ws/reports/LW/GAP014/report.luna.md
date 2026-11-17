STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_GAP014/AKLT/W/GAP014/Main.lean)
- This report: `/home/ubuntu/aklt/reports/LW/GAP014/report.md`

## Delivered declarations

`AKLT.W.GAP014.main_from_residuals` proves the target from two explicit residual propositions:

- `AKLT.W.GAP014.ProductTensorizationResidual`: rate-one Poincaré inequality for a strictly positive product law when the finite site set is nonempty. The empty-site case is proved in the file.
- `AKLT.W.GAP014.BoundedDensityComparisonResidual`: for a positive product reference with Poincaré constant one and a positive law satisfying `m q ≤ μ ≤ M q`, the one-ratio bound `PoincareLower μ (m / M)`.

The theorem statement is:

```lean
theorem AKLT.W.GAP014.main_from_residuals
    (hTensor : ProductTensorizationResidual)
    (hDensity : BoundedDensityComparisonResidual) :
    AKLT.Blueprint.Gap.SignedFrameBlockStatement
```

The proof normalizes every site weight, proves the signed edge factors lie in `[frameBound, 2-frameBound]`, bounds their product over exactly `E`, identifies the normalized interacting law as a tilt of the product reference, and simplifies the one-ratio constant to `frameRatio ^ E.card`. It handles empty `E` and empty `ι`. No arbitrary-pin positivity is used.

The requested unconditional declaration `AKLT.W.GAP014.main : AKLT.Blueprint.Gap.SignedFrameBlockStatement` is not delivered: the two residuals remain open, so I have not claimed a complete proof.

## Axioms

`#print axioms AKLT.W.GAP014.main_from_residuals`:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorry`, `admit`, or extra axiom is used.

## Build

- `lake env lean AKLT/W/GAP014/Main.lean` — passed, about 10 seconds.
- `lake build AKLT.W.GAP014.Main` — passed, 17.6 seconds wall time (Lean reported the module build at 9.1 seconds).

The compiler reports one style warning for the local `letI` used to discharge the empty-index case. There are no proof errors.

## Open issues

1. Prove `AKLT.W.GAP014.ProductTensorizationResidual` for nonempty finite site sets and arbitrary positive one-site laws. This is the commuting-coordinate heat-bath tensorization step.
2. Prove `AKLT.W.GAP014.BoundedDensityComparisonResidual`. This is the conditional-variance/Dirichlet lower comparison and constant-centering variance upper comparison under the pointwise density sandwich.
3. Then apply those proofs to `main_from_residuals` and export the requested unconditional `AKLT.W.GAP014.main`.

## ORCH-SUMMARY

- Delivered a compiled conditional proof in `AKLT/W/GAP014/Main.lean`.
- `main_from_residuals` has the exact signed-frame target conclusion, conditional on two closed residual Props.
- Site normalization, both signs of every edge factor, product interaction bounds, law normalization, and the final ratio are proved.
- The empty-site product case is proved; empty edge sets are included by finite-product reasoning.
- Open declarations: `ProductTensorizationResidual`, `BoundedDensityComparisonResidual`.
- The required unconditional `AKLT.W.GAP014.main` remains open; status is PARTIAL.
- Axioms are only `[propext, Classical.choice, Quot.sound]`; no placeholders or new axioms.
- `lake build AKLT.W.GAP014.Main` passed in 17.6 seconds wall time.
