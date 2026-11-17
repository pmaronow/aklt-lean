STATUS: PARTIAL

## Files

- `AKLT/W/H3C026/Main.lean`
- `/home/ubuntu/aklt/reports/LW/H3C026/report.md`

## Exported declarations

- `AKLT.W.H3C026.Residual_LegacyRowExpansion : Prop` is the explicit remaining row-expansion obligation. It asserts the packed `rowTerms` component equals the legacy `stationaryCoefficient` sum under the leaf's hypotheses.
- `AKLT.W.H3C026.centreZeroV2_proved : CertData.H3.Bridge.CentreZeroV2Leaf` proves that the legacy and V2 sums agree when the extended data vanishes at the centre.
- `AKLT.W.H3C026.main_from_residual (hrow : Residual_LegacyRowExpansion) : CertData.H3.Bridge.RowTermsV2Leaf` assembles the requested leaf from the residual and the checked centre-zero condition.
- `AKLT.W.H3C026.main (hrow : Residual_LegacyRowExpansion) : CertData.H3.Bridge.RowTermsV2Leaf` is the same conditional assembly. The required unconditional declaration `AKLT.W.H3C026.main : CertData.H3.Bridge.RowTermsV2Leaf` is not yet proved.

The main unresolved work is the legacy packed-row expansion: showing that ordinary, known-site, and dead-neighbor masks, pull lanes, and their rounded response coefficients produce the legacy stationary coefficient sum. The V2 centre-edge correction is handled separately by `centreZeroV2_proved`. No existing source or imported theorem in this worktree proves the residual.

## Axioms

From `#print axioms`:

- `AKLT.W.H3C026.centreZeroV2_proved`: `[propext, Classical.choice, Quot.sound]`
- `AKLT.W.H3C026.main_from_residual`: `[propext, Classical.choice, Quot.sound]`
- `AKLT.W.H3C026.main`: `[propext, Classical.choice, Quot.sound]`

No forbidden proof escape or extra axiom is used. The residual is a transparent `def`, and the conditional theorem states it explicitly.

## Build

- `lake build AKLT.W.H3C026.Main` — succeeded; Lean target build reported 7.9 seconds. No tests were run.

The brief requested the first attempt use a different cheaper model. This session has no model-switch control, so the proof attempt used the available model; this is the only process deviation.

## ORCH-SUMMARY

- Delivered the compiled file `AKLT/W/H3C026/Main.lean` and this report.
- Proved `centreZeroV2_proved`, which transports the legacy row sum to the corrected V2 row sum using the checked centre-zero value.
- The requested unconditional theorem `AKLT.W.H3C026.main : CertData.H3.Bridge.RowTermsV2Leaf` remains open.
- `AKLT.W.H3C026.Residual_LegacyRowExpansion` is the exact explicit residual; it covers packed lane and coefficient expansion through ordinary, known-site, and dead-neighbor terms.
- The available `AKLT.W.H3C026.main` is conditional on that residual and therefore does not satisfy the requested exact theorem type.
- Build: `lake build AKLT.W.H3C026.Main` succeeded in 7.9 seconds; exported theorem axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
- Model switch requested by the brief was unavailable in this session.
- Orchestrator should carry forward the residual proof obligation or supply a proved specialization of the legacy `RowTermsAgreement`.
