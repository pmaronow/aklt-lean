STATUS: PROVED FROM DEPS

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC065/AKLT/W/REC065/Main.lean): the completed proof and closed theorem.
- [Audit.lean](/home/ubuntu/aklt/wt/LW_REC065/AKLT/W/REC065/Audit.lean): independent exact-type and axiom checks.
- The earlier report remains in `report.luna.md`.

## Exported declarations

```lean
AKLT.W.REC065.main : AKLT.Blueprint.Rec.KernelLengthMajorantStatement
AKLT.W.REC065.shift_geometry : AKLT.Blueprint.Rec.ShiftGeometryStatement
AKLT.W.REC065.departure_budget : AKLT.W.REC065.Residual_DepartureBudget
```

The main statement is exactly the requested closed type:

```lean
∀ CV q : ℝ, OpenTrailBound CV q → ∀ θ : ℝ, q^2 < θ → θ ≤ 1 →
  ∀ X Y : PairType, ∀ n : ℕ,
    shiftedLength θ X Y n ≤ ENNReal.ofReal (kernelMajorant CV q θ n)
```

The retained transparent definitions are:

- `closedTrailMass (n : ℕ) (X : PairType) : ℝ`: the finite sum of true trail weights over closed trails of length `n` and type `X`.
- `Residual_DepartureBudget : Prop`: for every closed trail and departure, the sum of `responseKappa X Y s w i` over `s < n + 2` is at most `18094 / 100000 + 2 * (36751 / 100000 : ℝ)`. This proposition is now proved by `departure_budget`.
- `Residual_ClosedRowMajorant : Prop`: for `0 < θ ≤ 1`, the finite shifted coefficient sum is at most `n * (ᾱ + 2β̄) * θ^(-n/2-1) * closedTrailMass n X`. The existing private reduction proves it from the now-discharged departure budget.

No residual hypothesis remains on `main`.

## Proof and dependencies

Reused the previous attempt's geometric, exposure-product, finite-regrouping, and H2 comparison proofs. The missing local budget is supplied by supporting lemmas from `AKLT.W.REC070.TrailBound`, part of the proved REC070 leaf listed in `proved-index.tsv`:

- `AKLT.W.REC070.response_total`: summing all response types and finite shifts recovers the sum over live response pairs.
- `AKLT.W.REC070.pair_sum_cap`: that total is at most `ᾱ + 2β̄` for a trail. Its proof counts pairs among the three nonarrival neighbours: two pairs contain the outgoing neighbour, and one does not. Dead-neighbour deletion decreases the nonnegative sum; beta-prime is also bounded by beta-bar.

The fixed-type sum is below the total by nonnegativity. Casting the rational estimate proves `departure_budget`. The prior majorant reduction then produces the requested closed theorem. These dependency modules do not import REC065, so there is no dependency cycle. No frozen statement or file outside REC065 was edited.

## Validation

`PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.REC065.Main` succeeded. Lake reported 5.8 s for Main, plus 3.0 s for REC070.Foundations and 4.0 s for REC070.TrailBound. Existing style/deprecation lints are nonfatal.

`PATH="$HOME/.elan/bin:$PATH" /usr/bin/time -p lake env lean AKLT/W/REC065/Audit.lean` succeeded in 4.68 s wall time. It checks:

```lean
example : AKLT.Blueprint.Rec.KernelLengthMajorantStatement := AKLT.W.REC065.main
```

The output confirms the exact type and all exported theorem axioms:

```text
AKLT.W.REC065.main : AKLT.Blueprint.Rec.KernelLengthMajorantStatement
'AKLT.W.REC065.shift_geometry' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC065.departure_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC065.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

A source scan found no forbidden proof escapes. No mathematical obligations remain open.

## ORCH-SUMMARY

- Delivered the exact closed theorem `AKLT.W.REC065.main` in `AKLT/W/REC065/Main.lean`.
- Status: PROVED FROM DEPS; no additional premise on the theorem.
- Reused the earlier proof and discharged `AKLT.W.REC065.Residual_DepartureBudget`.
- Dependency: `AKLT.W.REC070.TrailBound`, supporting lemmas of indexed leaf REC070.
- Added `AKLT/W/REC065/Audit.lean` with the independent exact-type check.
- Build and audit both succeed; only permitted axioms occur.
- The legacy `Residual_*` definition names remain, but neither is an open obligation.
- No frozen files edited; no sub-agents used.
- Open: none. No orchestrator decision or follow-up proof is needed.
