STATUS: PROVED

## Files

- `AKLT/W/H3C019/Main.lean`

## Exported declaration

- `AKLT.W.H3C019.main : CertData.H3.Bridge.EndpointBoxLeaf`

The proof bounds each of the twelve compass-step coordinates between -1 and 1, sums those bounds, and translates the resulting displacement rectangle from `kernelStart = (-1, 0)`. It proves only the stated endpoint containment and does not normalize the certificate.

## Axioms

`#print axioms AKLT.W.H3C019.main`:

```text
[propext, Classical.choice, Quot.sound]
```

These are the allowed axioms. The proof uses no forbidden declarations or tactics (`sorry`, `admit`, `axiom`, `native_decide`, and related escapes).

## Build

- Command: `lake build AKLT.W.H3C019.Main`
- Result: successful.
- Elapsed: 19.459 s (the target module took 8.2 s; Lake reported 8973 jobs, including dependency replay).

## Open issues and deviations

The brief asks for a first attempt using a different cheaper model and also forbids sub-agents. This session provides no way to switch the active model without delegating, so I followed the no-sub-agents instruction and completed the proof in the active model. No proof issue remains.

## ORCH-SUMMARY

- Delivered `AKLT/W/H3C019/Main.lean` with `AKLT.W.H3C019.main` at the exact requested type.
- The exact endpoint-box leaf compiles successfully.
- Exported theorem axioms: `propext`, `Classical.choice`, `Quot.sound`.
- No forbidden proof declarations or tactics are used.
- No helper files were needed.
- No mathematical open issue remains.
- Limitation: the requested cheaper-model first attempt was unavailable without a sub-agent, which the brief forbids.
- Orchestrator: no further decision is needed for the proof; note the model-selection deviation if it matters to campaign policy.
