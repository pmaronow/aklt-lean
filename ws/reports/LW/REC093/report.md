STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC093/AKLT/W/REC093/Main.lean)
- This report: `/home/ubuntu/aklt/reports/LW/REC093/report.md`

## Exported declaration

- `AKLT.W.REC093.main : AKLT.Blueprint.Rec.BoundaryExampleCoveredStatementV2`

The proof builds the concrete pattern and its legacy finite-template matching data, then derives the shared non-tip status and internal-bond conditions. The reverse bond implication uses the actual pattern bond filter and its kept-set conditions; the tip case uses the shared matcher’s one-sided implication.

## Axioms

`#print axioms AKLT.W.REC093.main`:

```text
'AKLT.W.REC093.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.REC093.Main` — passed; Lean reported 5.6 seconds for the module (10.96 seconds elapsed for the command).

## Open issues and deviations

The requested cheaper-model first attempt was not run. The same brief also prohibits sub-agents, and no in-process model-switch tool is available in this session. No other open proof obligations remain.

## ORCH-SUMMARY

- Delivered `AKLT/W/REC093/Main.lean` with the exact exported theorem and type.
- The shared statement is proved from the concrete pattern, with legacy matching data reproved locally and translated to shared internal-bond conditions.
- `lake build AKLT.W.REC093.Main` passes.
- Axioms: `[propext, Classical.choice, Quot.sound]`.
- Deviation: no cheaper-model first attempt, due to the no-sub-agent constraint and lack of in-process model switching.
- No residual statements or open mathematical obligations.
