STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC081/AKLT/W/REC081/Main.lean)

## Exported declarations

- `AKLT.W.REC081.ResidualSecondTermProductBound`: the unresolved bound for `secondTerm` by the product of the two one-point decay factors at the original distances to `protectedSites`.
- `AKLT.W.REC081.ResidualProtectedDepthProjection`: converts the extended-natural pair depth hypothesis into lower bounds on both natural protected distances.
- `AKLT.W.REC081.main_of_residuals`: proves `AKLT.Blueprint.Rec.SecondTermBoundStatement` from those two explicit residual propositions, including the exact retained `sourceConstant` and exponent `q^(2*d)`.

The requested closed theorem `AKLT.W.REC081.main : AKLT.Blueprint.Rec.SecondTermBoundStatement` is not yet delivered. The residual product estimate contains the substantive second-term expansion and shared-matcher one-point work; it is stated transparently rather than assumed inside a theorem claiming the requested result.

## Axioms

`#print axioms AKLT.W.REC081.main_of_residuals`:

```text
'AKLT.W.REC081.main_of_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.REC081.Main` — succeeded; the Lean module compilation reported 4.9 s, and a subsequent cached build took 8.5 s wall time.
- Axiom inspection used `lake env lean /tmp/REC081Axioms.lean`.

## Open issues

- `AKLT.W.REC081.ResidualSecondTermProductBound` remains unproved. This requires the finite pair expansion/splitting, terminal auxiliary-network estimate with the V2 shared matcher and original pins/S, and the first-hit sum of pointwise maxima.
- `AKLT.W.REC081.ResidualProtectedDepthProjection` remains unproved. This is the conversion from finite extended-natural distances to the original-S natural distances under `PairData.depth`.
- Consequently the exact no-argument declaration `AKLT.W.REC081.main` is absent.

## ORCH-SUMMARY

- Delivered a compiling conditional assembly in `AKLT/W/REC081/Main.lean`.
- It preserves the exact `sourceConstant CV q` and `q^(2*d)` conclusion once the two residuals are supplied.
- Open: `ResidualSecondTermProductBound`, the main two-stage trail/one-point estimate.
- Open: `ResidualProtectedDepthProjection`, the depth-to-distance conversion.
- Deviation: the requested closed theorem `AKLT.W.REC081.main` is not proved; status is PARTIAL.
- Build passed: `lake build AKLT.W.REC081.Main`.
- `main_of_residuals` depends only on `[propext, Classical.choice, Quot.sound]`.
