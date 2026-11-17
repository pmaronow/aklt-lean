STATUS: PROVED FROM DEPS

## Files

- `/home/ubuntu/aklt/wt/LW_H3C015/AKLT/W/H3C015/Main.lean`
- `/home/ubuntu/aklt/wt/LW_H3C015/AKLT/W/H3C015/Counting.lean`
- Verification artifacts in this report directory: `Check.lean`, `build.log`, `check.log`.
- Earlier report retained as `report.luna.md`.

## Exported declarations

```lean
AKLT.W.H3C015.main : CertData.H3.Bridge.RawTrieCountLeaf
```

This has exactly the requested closed type, whose definition is:

```lean
∀ G : AKLT.Cert.H3.Production.Graph,
  (AKLT.Cert.H3.Production.rawBatch G 0 4096).count =
    Fintype.card (AKLT.Defs.MemoryWindow 10)
```

The helper module exports:

```lean
AKLT.W.H3C015.rawBatch_count_replays
  (G : AKLT.Cert.H3.Production.Graph) :
  (AKLT.Cert.H3.Production.rawBatch G 0 4096).count =
    ∑ c ∈ Finset.range (4 ^ 10),
      if (AKLT.Cert.H3.Production.replayRaw 10 c
        AKLT.Cert.H3.Production.rawInitial).isSome then 1 else 0
```

All other new declarations are private. The former `Residual_1` and the extra hypothesis on `main` have been removed.

## Proof and dependencies

`Counting.lean` proves the traversal-to-replay counting identity symbolically. It projects `RawStats.count` through the list fold, proves that replay splits into a prefix and suffix, and proves by induction that DFS counts each successful suffix code once. Partitioning a range into consecutive blocks connects the 4096 six-digit stems and their four-digit suffixes with all ten-digit codes. This argument works for every graph, independently of its data or check results.

`Main.lean` identifies successful ten-digit replays with raw windows, then uses the encode/decode bijection to identify the filtered code count with `Fintype.card (MemoryWindow 10)`.

The following imports are authorized proved leaves listed in `/home/ubuntu/aklt/state/lw/proved-index.tsv`:

| Module | Theorem | Statement |
| --- | --- | --- |
| `AKLT.W.H3C001.Main` | `AKLT.W.H3C001.main` | `CertData.H3.Bridge.CodeDecodeLeaf` |
| `AKLT.W.H3C002.Main` | `AKLT.W.H3C002.main` | `CertData.H3.Bridge.CodeEncodeLeaf` |
| `AKLT.W.H3C005.Main` | `AKLT.W.H3C005.main` | `CertData.H3.Bridge.RawReplaySoundLeaf` |
| `AKLT.W.H3C006.Main` | `AKLT.W.H3C006.main` | `CertData.H3.Bridge.RawReplayCompleteLeaf` |

No unproved blueprint leaves or residual assumptions remain. The proof uses structural induction and finite-sum identities; it never normalizes the whole certificate and uses no `native_decide`.

## Axioms

The modules contain `#print axioms` for both exported theorems. The separate import check reproduced:

```text
'AKLT.W.H3C015.main' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C015.rawBatch_count_replays' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C015.main : CertData.H3.Bridge.RawTrieCountLeaf
```

Only the permitted axioms occur.

## Validation

- `/usr/bin/time -f 'elapsed_seconds=%e' lake build AKLT.W.H3C015.Main` succeeded in **34.08 seconds**. The final new-module builds took approximately 10 seconds for `Counting` and 11 seconds for `Main`; see `build.log`.
- `/usr/bin/time -f 'elapsed_seconds=%e' lake env lean /tmp/H3C015-Check.lean` succeeded in **10.36 seconds**. The exact source is retained here as `Check.lean`; see `check.log`.
- The separate check contains `example : CertData.H3.Bridge.RawTrieCountLeaf := AKLT.W.H3C015.main`, the exact-type `#check`, and both axiom checks.
- The delivered sources contain none of the forbidden proof escapes and require no heartbeat or recursion-limit overrides.
- Source edits are confined to `AKLT/W/H3C015/`; reports and logs are in the assigned report directory.

## Open issues and workflow limitation

There are no mathematical open issues for this leaf. No sub-agents were used. This repair used the active model; a separate cheaper-model invocation was unavailable because this session exposes no model-switch tool. The earlier attempt remains documented in `report.luna.md`.

## ORCH-SUMMARY

- Delivered the exact closed theorem `AKLT.W.H3C015.main : CertData.H3.Bridge.RawTrieCountLeaf`.
- Status: PROVED FROM DEPS.
- Delivered helper: `AKLT.W.H3C015.rawBatch_count_replays`.
- Dependencies: `AKLT.W.H3C001.main`, `AKLT.W.H3C002.main`, `AKLT.W.H3C005.main`, `AKLT.W.H3C006.main`; all are in the proved index.
- Open mathematical leaves/residuals: none.
- Exact-type import check and requested Lake target both pass.
- Both exported theorems use only `propext`, `Classical.choice`, `Quot.sound`.
- No whole-certificate normalization or prohibited proof mechanism is used.
- Workflow deviation: no additional cheaper model was invoked; model switching was unavailable and sub-agents were forbidden.
- Orchestrator action: accept/register this leaf; retain the four indexed dependencies.
