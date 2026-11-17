STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_Q050/AKLT/W/Q050/Main.lean)
- This report: `/home/ubuntu/aklt/reports/LW/Q050/report.md`

## Exported declarations

- `AKLT.W.Q050.glueConfig` glues a `V` configuration into `W`, retaining the fixed `W` configuration outside `V`.
- `AKLT.W.Q050.Residual_FiberWeightFactorization : Prop` states that, under `interactionBounds` and proper colouring, `planeWeight` on the glued `W` configuration equals a positive constant times `planeWeight` on `V` with `inducedBoundary`.
- `AKLT.W.Q050.main_of_factorization : AKLT.W.Q050.Residual_FiberWeightFactorization → AKLT.Blueprint.Q.PlaneConditioningStatement` proves the requested conditioning identity from that explicit residual.

The required `AKLT.W.Q050.main : AKLT.Blueprint.Q.PlaneConditioningStatement` is not yet delivered. No counterexample was found; the remaining obligation is the finite-product factorization residual.

## Established proof steps

- `interactionBounds` and proper colouring give positivity of each interaction factor and hence of every `planeWeight`.
- The conditioned `W` configurations are in bijection with actual `V` configurations via `glueConfig` and restriction. The finite-sum argument proves that the conditional marginal is the normalization of the glued `W` weights.
- A positive constant factorization of those glued weights cancels under normalization, yielding the target law with `inducedBoundary`. The proof treats empty volumes and `V = W` through the same finite-sum statements.

## Axiom audit

`#print axioms AKLT.W.Q050.main_of_factorization`:

```text
'AKLT.W.Q050.main_of_factorization' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build and timing

- `lake build AKLT.W.Q050.Main` — succeeded; reported build time 11 s.
- `lake env lean /tmp/Q050Axioms.lean` — succeeded; reported wall time 8.1 s. The temporary audit file imports `AKLT.W.Q050.Main` and runs the `#print axioms` command above.

## Open issue

Prove `AKLT.W.Q050.Residual_FiberWeightFactorization`. Its missing proof must split the internal bonds of `W` into bonds internal to `V`, internal to the complement of `V` in `W`, and crossing bonds; identify crossing bonds with the corresponding original legs of `V` (reversing orientation where needed); and split original legs by source. The crossing and `V`-to-outside-`W` factors must match the factors in `planeWeight` with `inducedBoundary`, leaving a positive constant independent of the `V` configuration. Once established, `main_of_factorization` yields the requested `main` directly.

## ORCH-SUMMARY

- Delivered `AKLT/W/Q050/Main.lean` with positivity lemmas, the conditioned-fibre bijection, and `main_of_factorization`.
- Explicit remaining proposition: `AKLT.W.Q050.Residual_FiberWeightFactorization`.
- The exact requested theorem `AKLT.W.Q050.main` is not yet proved; status is `PARTIAL`.
- No files outside `AKLT/W/Q050/` and the requested report directory were edited.
- Build succeeded; `main_of_factorization` uses only `[propext, Classical.choice, Quot.sound]`.
- Orchestrator should pass on the residual edge/product decomposition proof; after proving it, instantiate `main_of_factorization` as `main`.
