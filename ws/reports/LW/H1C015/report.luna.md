STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1C015/AKLT/W/H1C015/Main.lean)

## Delivered declarations

- `AKLT.W.H1C015.Residual_sectorPackingExpansion : Prop` is the remaining certificate-independent mixed-radix identity, stated for any base network and sector network passing `sectorNetworkCheck`.
- `AKLT.W.H1C015.main_of_residual (hResidual : Residual_sectorPackingExpansion) : AKLT.Cert.H1.Production.Leaves.sectorPackingExpansion` proves the requested leaf from that residual. The proof extracts `sectorNetworkCheck` from `Bundle.LayoutAccepted`.
- Gaussian arithmetic helpers establish the raw multiplication formula, addition/scalar laws, distributivity, and append summation needed by a full expansion proof.

The requested unconditional declaration `AKLT.W.H1C015.main` is not present. The residual is the unproved core: expanding the packed local coordinates through the four-state ring product at disjoint mixed-radix exponents, then distributing and reindexing the center sum. No unproved fact is used as a theorem hypothesis except the explicitly named residual in `main_of_residual`.

## Axiom audit

`#print axioms main_of_residual`:

```text
[propext, Classical.choice, Quot.sound]
```

`#print axioms gaussian_mul_add_left`:

```text
[propext, Classical.choice, Quot.sound]
```

These are the allowed Lean axioms. There is no axiom audit for `main`, since the required unconditional theorem has not been proved.

## Build

- `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.H1C015.Main` — succeeded; module build reported 5.4 s (overall replay/build completed successfully).

## Open issue

Prove `AKLT.W.H1C015.Residual_sectorPackingExpansion`. The missing step is a structural mixed-radix polynomial expansion for the packed ring product, including a collision-free column reindexing and preservation of both Gaussian components. The center-pair and three-color sum must then be distributed over those columns.

## ORCH-SUMMARY

- Delivered `AKLT/W/H1C015/Main.lean`, compiling with no forbidden constructs.
- `main_of_residual` derives the requested leaf from `Residual_sectorPackingExpansion`.
- The exact unconditional theorem `AKLT.W.H1C015.main` remains open.
- Residual: `AKLT.W.H1C015.Residual_sectorPackingExpansion`.
- Build: `lake build AKLT.W.H1C015.Main` succeeded.
- `main_of_residual` and `gaussian_mul_add_left` use only allowed axioms: propext, Classical.choice, Quot.sound.
- Orchestrator: pass on the residual proof or continue the mixed-radix ring expansion.
