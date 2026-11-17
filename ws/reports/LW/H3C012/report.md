STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_H3C012/AKLT/W/H3C012/Main.lean`
- `/home/ubuntu/aklt/reports/LW/H3C012/report.md`

## Exported declaration

`AKLT.W.H3C012.main : CertData.H3.Bridge.RawTrieBoundsLeaf`

The proof follows the packed raw trie recursively. Accepted raw leaves satisfy the `rawRow` class bound. Rejected branches carry a packed span filled with class `3741`; `SpanRepresents` transfers that sentinel through the packed lanes to `classAt`. The root batch is split into 4096 stems and 256-entry spans, and the replayed prefix code is related to its corresponding raw code. The proof uses the imported `repeatLane_eq` and `lane_packFn` results from `AKLT.Gen.Packed.Basic`.

I read `RawTrieBoundsLeaf` and its relevant definitions in `CertData/H3/Bridge/Interface.lean`, the graph layout and production checker definitions, the packed lane definitions, and the p:automaton10 proposition in `app-input-contracts.tex`. The proof establishes the bound directly; it does not invoke `RawTrieCoverageLeaf`, which is a proposition definition rather than a proved theorem or hypothesis here.

## Axioms

`#print axioms main`:

```text
'AKLT.W.H3C012.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are within the allowed axiom set.

## Build

- Command: `lake build AKLT.W.H3C012.Main`
- Result: success; Lean reported `Built AKLT.W.H3C012.Main (4.4s)`.
- Full command wall time: 9.552s.
- The forbidden-shortcut scan found no proof shortcuts; its only match was the required `#print axioms main` line.

## Open issues and deviations

The brief required the first attempt to use a different, cheaper model. This session exposes no model-switch control, and the brief also prohibits sub-agents, so that requirement could not be met. I disclosed this before starting the proof. The suggested coverage-leaf route was not needed; the theorem is proved directly from the checker and span hypotheses.

## ORCH-SUMMARY

- Delivered `AKLT.W.H3C012.main` with the exact requested statement.
- `lake build AKLT.W.H3C012.Main` succeeds.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- The proof derives the class bound from accepted raw leaves and sentinel-filled rejected spans.
- Open exact names: none.
- Deviation: first-attempt cheaper-model requirement could not be met; no model-switch control was available and sub-agents were prohibited.
- The proof did not use `RawTrieCoverageLeaf`; direct checker reasoning sufficed.
- Orchestrator decision: none required for the proof; record the model-routing deviation if policy requires it.
