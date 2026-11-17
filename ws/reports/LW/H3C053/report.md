STATUS: PROVED

## Files

- `AKLT/W/H3C053/Main.lean`
- `/home/ubuntu/aklt/reports/LW/H3C053/report.md`

## Exported declaration

`AKLT.W.H3C053.main : CertData.H3.Bridge.RawShardJoinLeaf`

The proof factors a batch of `64 * 64` stems into its 64 batches of 64, using generic fold lemmas for `RawStats.add`. It then applies the receipt's shard equalities, per-shard success facts, and count sum. It does not unfold or normalize the whole raw graph certificate.

## Axioms

`#print axioms AKLT.W.H3C053.main`:

```text
'AKLT.W.H3C053.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All are allowed by the brief.

## Build

- `lake build CertData.H3.Bridge.Production` — about 24 seconds. The target module's `.olean` was absent in this worktree, so this built the missing import graph.
- `lake build AKLT.W.H3C053.Main` — 9.15 seconds; succeeded.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/H3C053/Main.lean` with the exact requested theorem and type.
- Status: proved from the receipt hypothesis using batch decomposition and fold properties.
- `#print axioms`: `[propext, Classical.choice, Quot.sound]`, all permitted.
- The requested Lake target built successfully; its missing dependency `.olean` required an initial dependency build.
- No residual statements or open issues.
