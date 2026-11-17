STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H3C016/AKLT/W/H3C016/Main.lean)
- This report: `/home/ubuntu/aklt/reports/LW/H3C016/report.md`

## Exported declaration

`AKLT.W.H3C016.main : CertData.H3.Bridge.EdgeCountLeaf`

The proof establishes the generic correspondence between the three `edgeCounts` fold coordinates and the quotient's straight, turn, and revisit labelled-edge counts, then applies the stated aggregate counts. It does not inspect or normalize any particular graph table.

## Axioms

`#print axioms AKLT.W.H3C016.main`:

```
[propext, Classical.choice, Quot.sound]
```

These are the allowed Lean axioms.

## Build

- Command: `lake build AKLT.W.H3C016.Main`
- Result: success; Lake reported the target module built in 11 s (overall command 15.6 s).

## Open issues and deviations

The requested first attempt with a different cheaper model could not be routed: this interface exposed no model-selection control, and the task brief forbids sub-agents. I proceeded with the available model. No proof obligations remain open.

## ORCH-SUMMARY

Delivered `AKLT/W/H3C016/Main.lean` with `AKLT.W.H3C016.main` proving `CertData.H3.Bridge.EdgeCountLeaf`.
Build succeeded with `lake build AKLT.W.H3C016.Main`.
Axioms: `propext`, `Classical.choice`, `Quot.sound` (allowed).
The proof relates the generic edge-count fold to the quotient counts; no graph literal was evaluated.
Deviation: cheaper-model first-attempt routing was unavailable in this interface; sub-agents were disallowed.
Open declarations: none. Orchestrator decision: none required.
