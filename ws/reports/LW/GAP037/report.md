STATUS: PROVED

Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_GAP037/AKLT/W/GAP037/Main.lean): exports the exact requested theorem.
- [Basic.lean](/home/ubuntu/aklt/wt/LW_GAP037/AKLT/W/GAP037/Basic.lean): finite fibre conditioning, normalization under rescaling and equivalence, and the adjacent parity calculation.
- [Geometry.lean](/home/ubuntu/aklt/wt/LW_GAP037/AKLT/W/GAP037/Geometry.lean): halo injectivity and the bijection between lifted edges and local frozen torus bonds.
- [Weights.lean](/home/ubuntu/aklt/wt/LW_GAP037/AKLT/W/GAP037/Weights.lean): factor identities, positivity, and the raw-weight factorization.
- [Audit.lean](/home/ubuntu/aklt/wt/LW_GAP037/AKLT/W/GAP037/Audit.lean): an independent exact-type example, declaration signatures, and axiom checks for every exported theorem.

Exported declarations and statements

```lean
theorem AKLT.W.GAP037.main : AKLT.Blueprint.Gap.BoxGaugeLawStatement
```

The complete exact Lean signatures of all 54 exported declarations (47 theorems and 7 definitions), together with each theorem's axiom output, are in [audit.log](/home/ubuntu/aklt/reports/LW/GAP037/audit.log). The principal helper statements are:

- `blockLaw_formula`: the conditional block marginal equals the normalized weight obtained by inserting the free coordinates into the fixed exterior.
- `blockLaw_normalize_formula`: the same formula for an initially normalized weight, provided its global partition sum is nonzero.
- `paritySign_adjacent`: `Adjacent x y → paritySign x = -paritySign y`.
- `normalize_rescale_equiv`: if `f x = c * g (e x)` for a finite equivalence `e` and `c ≠ 0`, then `normalize f x = normalize g (e x)`.
- `reduction_inj_halo`: `2*M+3 ≤ L.val` and `2*M+3 ≤ N.val` imply injectivity of reduction on `square a (M+1)`.
- `coordinates_image`: the image under reduction of the lifted square equals the labelled torus square specified by `BoxCoordinates`.
- `edgeBond_injective` and `edgeBond_surjective`: reduction gives a bijection from the union of internal bonds and original legs of the lifted square onto the frozen torus bonds touching its image, using halo injectivity and `LiftBonds`.
- `gauge_factor` and `gauge_product`: the signed coordinate change converts every local torus interaction factor, and their product, into the corresponding plane interaction.
- `torusFactor_pos` and `torusWeight_pos`: the supplied signed-interaction positivity and proper colouring make all torus factors and weights strictly positive.
- `exterior_factor`: a torus bond outside the block has a factor independent of the inserted free assignment.
- `liftedWeightFactorization`: under interaction positivity, proper colouring, `BoxCoordinates`, `LiftBonds`, and halo injectivity, there exists `c > 0`, independent of the block assignment `ω`, such that
  `torusWeight L N κ (insertBlock Q σ ω) = c * planeWeight (κ ∘ reduction L N) W (fun z => C.boundary σ z) (C.change.configurations ω)`.

Proof

The conditional marginal is first reindexed by the free block assignments. Halo injectivity follows directly from the integer coordinate bounds and the periods. The exact bond data and the existing proved uniqueness of frozen torus bonds identify each internal or crossing factor exactly once. Adjacent lifted signs have product minus one, so each torus factor equals its ferromagnetic plane factor. The factors wholly outside the block are independent of the free assignment and strictly positive. Together with the ratio of constant site weights, they form the positive scalar in `liftedWeightFactorization`; normalization cancels this scalar. Signs are defined only on plane lifts.

Axioms

```text
'AKLT.W.GAP037.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Audit.lean` checks every exported theorem. All 47 report only permitted axioms; see the complete output in `audit.log`.

Validation

- `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.GAP037.Main` — passed, 25.73 seconds wall time for the final build; module times: Basic 4.8 s, Geometry 6.5 s, Weights 5.3 s, Main 3.0 s. Full output: [build.log](/home/ubuntu/aklt/reports/LW/GAP037/build.log).
- `PATH="$HOME/.elan/bin:$PATH" lake env lean AKLT/W/GAP037/Audit.lean` — passed, 6.06 seconds wall time. This includes `example : AKLT.Blueprint.Gap.BoxGaugeLawStatement := AKLT.W.GAP037.main`.
- No forbidden proof constructs or residual assumptions remain. No tracked existing project file was changed; the leaf files are under `AKLT/W/GAP037/`.

Open issues

None. The earlier residual reduction has been replaced by a proof of the requested closed statement. The original earlier report is retained as `report.luna.md`.

ORCH-SUMMARY

- STATUS: PROVED.
- Delivered `AKLT.W.GAP037.main : AKLT.Blueprint.Gap.BoxGaugeLawStatement`.
- Main module: `AKLT/W/GAP037/Main.lean`.
- Helpers: `Basic.lean`, `Geometry.lean`, `Weights.lean`; verification: `Audit.lean`.
- Both finite conditioning and raw-weight factorization are proved.
- Positive exterior-only factors are proved nonzero before cancellation.
- No global torus bipartition is assumed.
- No open residual statements, additional premises, or deviations.
- Main build and independent exact-type check passed.
- All 47 exported theorems audited; only propext, Classical.choice, Quot.sound occur.
- Orchestrator can use the exact requested theorem; no further decision is required.
