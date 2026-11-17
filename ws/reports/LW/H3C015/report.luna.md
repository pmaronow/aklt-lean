STATUS: PARTIAL

## Files

- `/home/ubuntu/aklt/wt/LW_H3C015/AKLT/W/H3C015/Main.lean`

## Declarations

- `AKLT.W.H3C015.rawCodes10 : Finset (Fin (4 ^ 10))` filters codes whose decoded word satisfies `RawWindow`.
- `AKLT.W.H3C015.Residual_1 : Prop` is `∀ G : Graph, (rawBatch G 0 4096).count = AKLT.W.H3C015.rawCodes10.card`.
- `AKLT.W.H3C015.main : AKLT.W.H3C015.Residual_1 → CertData.H3.Bridge.RawTrieCountLeaf` proves the requested leaf from that residual.
- Private helpers prove the length‑10 encode/decode round trips and identify `Fintype.card (MemoryWindow 10)` with the finite code-set cardinality.

The requested unconditional type `AKLT.W.H3C015.main : CertData.H3.Bridge.RawTrieCountLeaf` is not yet proved.

## Axioms

`#print axioms AKLT.W.H3C015.main`:

```text
[propext, Classical.choice, Quot.sound]
```

These are permitted axioms. The proof of the unconditional leaf remains open because it depends on `Residual_1`.

## Build

- `lake build AKLT.W.H3C015.Main` — succeeded, 19 seconds (8974 jobs replayed; the new module built successfully).

## Open issue

- Prove `AKLT.W.H3C015.Residual_1`: `(rawBatch G 0 4096).count = rawCodes10.card` for every `G`. This is the traversal-to-valid-code enumeration lemma. Direct kernel reduction of the whole `rawBatch` recursion exceeded the configured 2,000,000 heartbeat limit; no such reduction is used in the delivered proof.
- The requested first attempt with a different cheaper model could not be made because this session exposes no model switch, and the task forbids sub-agents. Work proceeded with the available session after requesting clarification and receiving no answer.
- The suggested universal `RawReplaySoundLeaf`, `RawReplayCompleteLeaf`, and `CodeEncodeLeaf` were not delivered as proved lemmas; only the length‑10 code round trips needed for the finite-type equivalence were proved.

## ORCH-SUMMARY

- Delivered a compiled partial module at `AKLT/W/H3C015/Main.lean`.
- The file proves the requested leaf from the explicit residual `AKLT.W.H3C015.Residual_1`.
- Open: prove `AKLT.W.H3C015.Residual_1`; then make `AKLT.W.H3C015.main` unconditional with the exact requested type.
- `lake build AKLT.W.H3C015.Main` succeeds; printed axioms are permitted.
- Limitation: the cheaper-model first attempt was unavailable; no sub-agent was used, consistent with the task’s no-sub-agent rule.
- Orchestrator decision: pass on `Residual_1` for a focused proof attempt; if restarting the task, provide a model-selection route or authorize use of the available model.
