STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H3C006/AKLT/W/H3C006/Main.lean)
- `/home/ubuntu/aklt/reports/LW/H3C006/report.md`

## Exported declaration

- `AKLT.W.H3C006.main : CertData.H3.Bridge.RawReplayCompleteLeaf`

The proof establishes a stronger result: for every `n` and `c`, if `decodeWord n c` is a `RawWindow`, then `replayRaw n c rawInitial` is `some` a walk. The helper `SafePath` tracks that every remaining bond is absent from the walk's used-bond list and that remaining bonds are pairwise distinct. The step induction matches the first decoded digit to the first replay step, then transports freshness and injectivity to the tail path.

This direct argument makes `CodeDecodeLeaf` and `CodeEncodeLeaf` unnecessary; the numeric bounds in the target are unused. No certificate is normalized and `native_decide` is not used.

## Axioms

`#print axioms main`:

```text
'AKLT.W.H3C006.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the permitted axioms.

## Build

- `lake env lean AKLT/W/H3C006/Main.lean` — succeeded, 12.6 s.
- `lake build AKLT.W.H3C006.Main` — succeeded; 17.5 s wall time including dependency replay, with the target module reported at 7.7 s.

## Open issues and deviations

- No proof issue remains.
- The requested first attempt with a different cheaper model could not be performed: this runtime exposes no model-switch operation, and the campaign explicitly disallows sub-agents. The proof was authored and checked in the current runtime.
- The suggested encode/decode-leaf route was not needed because the replay argument proves the stronger unbounded statement directly.

## ORCH-SUMMARY

- Delivered `AKLT/W/H3C006/Main.lean` with the exact requested theorem name and type.
- `lake build AKLT.W.H3C006.Main` succeeded.
- `main` depends only on `propext`, `Classical.choice`, and `Quot.sound`.
- Replay completion is proved for arbitrary `n` and `c` from `RawWindow (decodeWord n c)`; target bounds are unused.
- `CodeDecodeLeaf` and `CodeEncodeLeaf` were not needed.
- Model-switch deviation: no model-switch tool was available; no sub-agent was used per campaign instruction.
- No open proof obligations; orchestrator can accept the proof and note the model-selection deviation.
