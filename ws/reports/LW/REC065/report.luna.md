STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC065/AKLT/W/REC065/Main.lean)

## Declarations

- `AKLT.W.REC065.shift_geometry : AKLT.Blueprint.Rec.ShiftGeometryStatement` is proved. The proof bounds distances from a response site to both endpoints by the path prefix and suffix, then takes the supremum over the pair.
- `AKLT.W.REC065.Residual_DepartureBudget : Prop` is the remaining local obligation:

  ```lean
  ∀ n X Y w, ClosedTrail X w → ∀ i : Fin n,
    (∑ s ∈ Finset.range (n + 2), (responseKappa X Y s w i : ℝ)) ≤
      (18094 / 100000 + 2 * (36751 / 100000 : ℝ))
  ```

- `AKLT.W.REC065.main : AKLT.W.REC065.Residual_DepartureBudget → AKLT.Blueprint.Rec.KernelLengthMajorantStatement` is proved. Given the residual, it proves the requested estimate using first-visit ordering, the full exposure product, closed-trail inclusion in H2, and finite ENNReal regrouping.

The remaining step is the finite pair count at one departure: show that the total coefficients over all shifts and a fixed type are bounded by `alpha-bar + 2 beta-bar`. In the paper this uses at most one alpha pair and two beta pairs, with the one-neighbour case bounded by beta-prime. No premise is added to the blueprint statement itself; the residual is an explicit hypothesis of the partial theorem.

## Axioms

`#print axioms AKLT.W.REC065.shift_geometry`:

```text
'AKLT.W.REC065.shift_geometry' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`#print axioms AKLT.W.REC065.main`:

```text
'AKLT.W.REC065.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.REC065.Main` — completed successfully; the module compiled in about 4.9 s (11.7 s wall time for the Lake command with the rest of the project already built).

## Open issues

- Prove `AKLT.W.REC065.Residual_DepartureBudget` from the finite response-pair definition and coefficient table. Until then, `AKLT.W.REC065.main` has a conditional type and does not satisfy the exact requested closed theorem type.
- No forbidden proof escapes or axioms were introduced.

## ORCH-SUMMARY

- Delivered `AKLT/W/REC065/Main.lean`; it builds.
- Proved `AKLT.W.REC065.shift_geometry` and the majorant reduction conditional on `AKLT.W.REC065.Residual_DepartureBudget`.
- Open: prove `AKLT.W.REC065.Residual_DepartureBudget`, the local coefficient sum/count bound.
- Deviation: `AKLT.W.REC065.main` takes that residual explicitly instead of having the requested closed type.
- Orchestrator should pass on the local coefficient-count obligation or assign its proof; no further user decision is needed.
