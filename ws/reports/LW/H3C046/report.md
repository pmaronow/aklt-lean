STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H3C046/AKLT/W/H3C046/Main.lean)

## Exported declaration

`AKLT.W.H3C046.main : CertData.H3.Bridge.PrefixFamilyJoinLeaf`

The proof establishes the generic interval split used by `PrefixResultsJoinLeaf`, then applies it to the consecutive group batches. The interval checker supplies the bounds needed by `PrefixBatchSoundLeaf`; the early DFS and checked batches are assembled with the exact `PrefixResult` fold. Certificate data is left parametric.

## Axiom audit

`#print axioms AKLT.W.H3C046.main`:

```text
'AKLT.W.H3C046.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are allowed axioms. The proof uses no `sorry`, `admit`, `axiom`, `native_decide`, or certificate normalization.

## Build

- Command: `lake build AKLT.W.H3C046.Main`
- Result: succeeded (exit code 0).
- Timing: 25.7 s wall time for the Lake command; target module reported 13 s.

## Open issues

No proof issue remains. The instruction to make the first attempt with a different cheaper model could not be acted on: this interface has no self-model switching tool, and the campaign instruction forbids sub-agents.

## ORCH-SUMMARY

- Delivered `AKLT.W.H3C046.main` with the exact requested statement.
- Added only `AKLT/W/H3C046/Main.lean` and this report.
- Verified with `lake build AKLT.W.H3C046.Main` (success).
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- Open proof names: none.
- Limitation: could not select a different cheaper model in this interface; no sub-agent was used under the no-sub-agent rule.
- Orchestrator action: no proof follow-up needed; decide whether to record the model-selection limitation.
