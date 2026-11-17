STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H3C018/AKLT/W/H3C018/Main.lean)
- `/home/ubuntu/aklt/reports/LW/H3C018/report.md`

## Exported declaration

`AKLT.W.H3C018.main : CertData.H3.Bridge.RectangleLeaf`

The proof identifies the endpoint coordinates with the corresponding row and column in the cropped packed plane. It proves a reusable 25-lane chunk extraction fact, then applies the existing packed lane and shift lemmas to the rows selected by `rectangle`. The `Fits P 80 19881` hypothesis is not needed; this argument proves the leaf for every `P`.

## Axioms

Output of `#print axioms AKLT.W.H3C018.main`:

```text
'AKLT.W.H3C018.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

Command: `export PATH="$HOME/.elan/bin:$PATH"; time lake build AKLT.W.H3C018.Main`

Result: success. Lake reported the target built in 6.8 seconds; total command wall time was 11.324 seconds.

## Open issues and deviations

- No mathematical proof issues remain.
- The requested first attempt using a different cheaper model was unavailable in this runtime: it exposes no model-switch control, and the brief prohibits sub-agents. The proof was completed with the active model.

## ORCH-SUMMARY

- Delivered `AKLT.W.H3C018.main : CertData.H3.Bridge.RectangleLeaf` in `AKLT/W/H3C018/Main.lean`; requested Lake build succeeds.
- Open proof names: none.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- The proof establishes the stronger statement for arbitrary `P`, without using `Fits P 80 19881`.
- Deviation: cheaper-model-first was unavailable; no sub-agents were used. Orchestrator should decide whether to accept this process deviation.
