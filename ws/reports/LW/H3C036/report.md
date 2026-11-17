STATUS: PROVED

## Files

- `AKLT/W/H3C036/Main.lean`
- `/home/ubuntu/aklt/reports/LW/H3C036/report.md`

## Exported declaration

`AKLT.W.H3C036.main : CertData.H3.Bridge.PrefixPartitionLeaf`

All supporting definitions and proofs in `Main.lean` are private. The proof establishes the base‑4 word/code bijections, reindexes the prefix and suffix code sums to direction words, and splits the finite closed-trail row at `depth`. It treats `closedContribution` and the potential values as exact summands, without unfolding the full certificate or changing their ordering semantics.

## Axioms

`#print axioms AKLT.W.H3C036.main`:

```text
[propext, Classical.choice, Quot.sound]
```

These are permitted axioms. The delivered file contains no `sorry`, `admit`, or `native_decide`.

## Build

Command: `lake build AKLT.W.H3C036.Main`

Result: successful; Lean reported `Built AKLT.W.H3C036.Main (5.2s)`. Full command wall time was 9.836s, including dependency replay.

## Open issues and deviations

No proof issues remain. The requested cheaper-model first attempt could not be made because this session exposes no model-switch tool; the brief also forbids sub-agents. I proceeded with a lightweight proof search in the current session.

## ORCH-SUMMARY

- Delivered `AKLT/W/H3C036/Main.lean` with `AKLT.W.H3C036.main` at the exact requested type.
- The theorem proves `CertData.H3.Bridge.PrefixPartitionLeaf` for all stated inputs and depths.
- Private helpers prove/reuse the exact `CodeEncodeLeaf` and `CodeDecodeLeaf` propositions and partition the finite sums by base‑4 codes.
- Build passed: `lake build AKLT.W.H3C036.Main` (5.2s module; 9.836s overall).
- `#print axioms`: `[propext, Classical.choice, Quot.sound]`.
- Open items: none.
- Deviation: alternate cheaper model was unavailable; no sub-agents were used, per brief.
