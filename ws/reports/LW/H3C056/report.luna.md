STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H3C056/AKLT/W/H3C056/Main.lean)

## Exported declarations

- `AKLT.W.H3C056.Residual_V2RowAgreement : Prop`: the generic packed row identity with `stationaryCoefficientV2` in place of the legacy coefficient. This is the remaining routing, mask, pull, and response-table calculation.
- `AKLT.W.H3C056.main (hV2 : Residual_V2RowAgreement) : AKLT.Cert.H3.RowTermsAgreement`: transfers that corrected row identity to the frozen legacy statement. At an edge whose destination is the centre, the supplied zero-centre lane makes the value zero; at other destinations the legacy and V2 coefficients agree.

The requested unconditional declaration `AKLT.W.H3C056.main : AKLT.Cert.H3.RowTermsAgreement` is therefore **not** delivered; `main` is conditional on the residual above.

## Axioms

`#print axioms AKLT.W.H3C056.main`:

```text
[propext, Classical.choice, Quot.sound]
```

No forbidden proof escape is used. The reported axiom set is the conditional transfer theorem's set.

## Build

`lake build AKLT.W.H3C056.Main` completed successfully. The Main module took 9.1 s; total wall time including replay was about 21 s.

## Open issue

Prove `AKLT.W.H3C056.Residual_V2RowAgreement` to obtain the requested unconditional leaf. In particular, the general packed-lane/mask calculation and exact response-table correspondence remain open. The V2 formulation keeps the corrected zero-centre-edge semantics; the legacy known-site centre edge is handled by the centre-zero lane in the proved wrapper.

The brief also required the first written proof attempt to come from a different cheaper model, while its common delivery rules prohibit sub-agents. This session has no direct model-switch operation. I did not write the core residual proof; the file contains only its transparent statement and the conditional centre-zero refinement.

## ORCH-SUMMARY

- Delivered `AKLT/W/H3C056/Main.lean` and this report.
- `Residual_V2RowAgreement` is the exact remaining conditional premise.
- `main` is conditional and does not have the requested unconditional type.
- Centre-zero transfer from V2 to the legacy coefficient is compiled and proved.
- Build: `lake build AKLT.W.H3C056.Main`, successful.
- Axioms of conditional theorem: `propext`, `Classical.choice`, `Quot.sound`.
- Open: packed routing/mask/pull and response-table identity in `Residual_V2RowAgreement`.
- Limitation: first-attempt model constraint could not be met alongside the no-subagents rule and unavailable model switching.
- Orchestrator decision: provide a cheaper-model first attempt or authorize a later proof attempt of the residual.
