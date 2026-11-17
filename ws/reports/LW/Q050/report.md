STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_Q050/AKLT/W/Q050/Main.lean): positivity, the actual-configuration fibre bijection, normalization, and the requested theorem.
- [Edges.lean](/home/ubuntu/aklt/wt/LW_Q050/AKLT/W/Q050/Edges.lean): canonical edge orientations and the complete fixed-factor product identity.
- [Check.lean](/home/ubuntu/aklt/reports/LW/Q050/Check.lean): independent exact-type check and axiom audit.

## Exported declarations

```lean
theorem AKLT.W.Q050.main : AKLT.Blueprint.Q.PlaneConditioningStatement
```

This is exactly the frozen statement: under `interactionBounds` and proper plane colouring, for every `V ⊆ W`, exterior boundary `η`, and configuration `σ`,

```lean
conditionalPlaneLaw κ W V η σ =
  planeLaw κ V (inducedBoundary W V η σ)
```

The helper module also exports the following declarations (using `AKLT.Defs` notation):

```lean
def AKLT.W.Q050.glueConfig {W V : Finset Plane} (_hVW : V ⊆ W)
    (σ : PlaneConfiguration W) (v : PlaneConfiguration V) : PlaneConfiguration W

theorem AKLT.W.Q050.fiberWeightFactorization
    (κ : Plane → Fin 3) (W : Finset Plane) (η : FrameBoundary W)
    (V : Finset Plane) (hVW : V ⊆ W) (σ : PlaneConfiguration W) :
    ∃ c : ℝ, ∀ v : PlaneConfiguration V,
      planeWeight κ W η (glueConfig hVW σ v) =
        c * planeWeight κ V (inducedBoundary W V η σ) v
```

All other helper declarations are private. No residual propositions remain.

## Proof

Every internal bond and original boundary leg is reindexed by its positive orientation. The reindexing is injective on boundary legs, disjoint from internal bonds, and preserves interaction factors by symmetry of the scalar product. The resulting finite edge set consists precisely of positive nearest-neighbour edges meeting the volume, so inclusion of volumes implies inclusion of edge sets.

For a glued configuration, every edge meeting `V` has exactly the letters supplied by the smaller configuration and `inducedBoundary`; every remaining edge has fixed letters. Splitting the finite product proves `fiberWeightFactorization`, including the site-weight power. This algebraic identity requires no numerical interaction assumptions.

The explicit `interactionBounds` premise gives positivity of all weights. Evaluating the factorization at a baseline configuration therefore proves that its multiplier is positive. The existing fibre bijection identifies the conditional marginal with normalization over actual `V` configurations, and the positive multiplier cancels.

The proof allows `V = ∅`, `V = W`, and `W = ∅` without extra hypotheses. Boundaries remain functions on exterior sites, preserving one shared letter at an exterior neighbour adjacent to several sites. No other blueprint leaves are used as lemmas. The earlier attempt's fibre and normalization proofs were reused; its unproved residual and `main_of_factorization` were replaced by the unconditional requested theorem.

## Axiom audit

`lake env lean /home/ubuntu/aklt/reports/LW/Q050/Check.lean` printed:

```text
AKLT.W.Q050.main : AKLT.Blueprint.Q.PlaneConditioningStatement
'AKLT.W.Q050.main' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q050.fiberWeightFactorization' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q050.glueConfig' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The audit also compiles:

```lean
example : AKLT.Blueprint.Q.PlaneConditioningStatement := AKLT.W.Q050.main
```

## Build commands and timings

With `PATH="$HOME/.elan/bin:$PATH"`, Lean `v4.35.0-rc2`:

- `lake build AKLT.W.Q050.Main` — successful, no warnings; 16.04 seconds wall time (Edges: 6.6 seconds; Main: 3.6 seconds).
- `lake env lean /home/ubuntu/aklt/reports/LW/Q050/Check.lean` — successful exact-type and axiom checks; 3.87 seconds wall time.
- Source scan found none of the forbidden proof constructs. No project files outside `AKLT/W/Q050/` were edited.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/Q050/Main.lean` and helper `AKLT/W/Q050/Edges.lean`.
- Required theorem: `AKLT.W.Q050.main : AKLT.Blueprint.Q.PlaneConditioningStatement`.
- Status: PROVED; no residuals, additional premises, or unavailable blueprint dependencies.
- Canonical edge products prove the complete fibre factorization.
- Empty volumes, equal volumes, and shared exterior neighbours are included.
- Exact-type check and `lake build AKLT.W.Q050.Main` both passed.
- All exported declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
- No limitations or deviations; no orchestrator decisions or follow-up work required.
