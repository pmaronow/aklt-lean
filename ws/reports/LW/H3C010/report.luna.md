STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H3C010/AKLT/W/H3C010/Main.lean)

## Delivered declarations

- `AKLT.W.H3C010.Residual_1 : Prop` — for any represented graph and any checked raw stem `p`, the 256 associated class entries are below 3741 exactly for raw windows.
- `AKLT.W.H3C010.main_of_residual (hResidual : Residual_1) : CertData.H3.Bridge.RawTrieCoverageLeaf` — reduces the batch statement to that stem-local residual. Its proof extracts each stem's `ok` bit from the folded `rawBatch` result and decomposes each code as `(c / 256) * 256 + c % 256`.
- Private proved helpers show that checked constant spans force sentinel classes, `rawRow=true` forces the class bound, every checked `rawDFS` branch has `ok=true`, and a checked depth-at-most-four DFS classifies a suffix exactly by whether `replayRaw` succeeds.

The requested unconditional declaration `AKLT.W.H3C010.main` is not delivered. `ResidualStemCoverage` remains unproved; it is the local DFS/replay coverage argument for one 256-code stem.

## Axioms

`#print axioms main_of_residual`:

```text
'AKLT.W.H3C010.main_of_residual' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are within the allowed axiom set. No `sorry`, `admit`, `axiom`, `native_decide`, or other forbidden escape appears in the delivered file.

## Build

- `lake build AKLT.W.H3C010.Main` — passed after the final code changes; the invocation took 10.3 s wall time, with the target module reported at 5.5 s. Existing dependencies were replayed by Lake.

## Open issue

Prove `Residual_1`. The recursive depth-four DFS classification and sentinel-span/terminal-row consequences are now proved. The remaining glue is to connect the six-step prefix replay and the four-step suffix replay to `replayRaw 10` for code `p * 256 + r`, then use the requested `RawReplaySoundLeaf` and `RawReplayCompleteLeaf` to connect success to `RawWindow`. Those replay leaves were inspected but not proved in this attempt.

The requested first attempt with a different cheaper model was unavailable through this session's model/tool controls; work proceeded with the available model.

## ORCH-SUMMARY

- Delivered `AKLT/W/H3C010/Main.lean` with a compiled conditional reduction.
- Open residual: `AKLT.W.H3C010.Residual_1`.
- The exact unconditional theorem `AKLT.W.H3C010.main` remains open.
- Batch folding and code-range decomposition are proved.
- The generic depth-four DFS classification is proved; replay split/glue and `RawReplaySoundLeaf`/`RawReplayCompleteLeaf` remain open.
- `lake build AKLT.W.H3C010.Main` passes.
- No new model could be selected for the requested cheaper-model first attempt.
- Orchestrator should continue by proving the local stem residual or pass it to a Lean proof effort.
