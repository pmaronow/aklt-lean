STATUS: PROVED

## Files

- `AKLT/W/H3C044/Main.lean`
- `/home/ubuntu/aklt/reports/LW/H3C044/report.md`

No existing project files were changed.

## Exported declarations

- `AKLT.W.H3C044.resultAddLeaf : CertData.H3.Bridge.ResultAddLeaf`
- `AKLT.W.H3C044.semanticBatchSplitLeaf : CertData.H3.Bridge.SemanticBatchSplitLeaf`
- `AKLT.W.H3C044.main : CertData.H3.Bridge.PrefixResultsJoinLeaf`

The result-value helper proves additivity of `resultValue` over `PrefixResult.add`. The semantic split helper uses the contiguous intervals certified by `intervalCheck`, `List.range_add`, and addition of rational batch sums. The main theorem gets each batch's `.ok` flag from the folded result's `.ok = true`, derives each interval's upper bound, applies the three supplied soundness/partition hypotheses, and identifies the resulting sum with `replayedResult`.

## Axioms

`#print axioms` output for each exported theorem:

```text
AKLT.W.H3C044.resultAddLeaf depends on [propext, Classical.choice, Quot.sound]
AKLT.W.H3C044.semanticBatchSplitLeaf depends on [propext, Classical.choice, Quot.sound]
AKLT.W.H3C044.main depends on [propext, Classical.choice, Quot.sound]
```

These are the permitted axioms listed in the brief.

## Build

Command:

```text
lake build AKLT.W.H3C044.Main
```

Result: successful. Final command wall time was 19.45 seconds (the target module reported 8.4 seconds; the command replayed cached dependencies).

## Open issues and deviations

No proof issues remain. The brief's request that the first attempt use a different cheaper model could not be carried out in this session: the current agent's model is fixed, and the task brief explicitly prohibits sub-agents. The proof and build were completed in this session.

## ORCH-SUMMARY

- Delivered `AKLT.W.H3C044.main` with the exact requested type in `AKLT/W/H3C044/Main.lean`.
- Also proved and exported the `ResultAddLeaf` and `SemanticBatchSplitLeaf` helper results.
- The requested Lake build succeeds; all exported theorem axiom sets are `[propext, Classical.choice, Quot.sound]`.
- No existing files were modified; no proof issues remain.
- Deviation: no cheaper-model first attempt was possible under the session's fixed model and no-sub-agents constraint.
- Orchestrator action: include the new Lean file and this report.
