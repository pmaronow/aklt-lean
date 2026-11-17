STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H3C034/AKLT/W/H3C034/Main.lean)
- `/home/ubuntu/aklt/reports/LW/H3C034/report.md`

## Delivered declarations

- `AKLT.W.H3C034.PrefixStemSoundResidual : Prop` is the explicit remaining obligation: for one valid prefix code, with the original exactness, quotient-correctness, endpoint-binding, depth, code-range, and evaluator-`ok` premises, `prefixStem`'s rational result equals `semanticStem`.
- `AKLT.W.H3C034.main (hStem : PrefixStemSoundResidual) : CertData.H3.Bridge.PrefixBatchSoundLeaf` proves that this one-stem obligation implies the requested batch statement. The proof establishes result-value additivity over the batch fold, extracts each stem's `ok` bit, and identifies the semantic batch with the sum of its stems.

This is not the requested unconditional `main : PrefixBatchSoundLeaf`; the residual remains unproved. It is a one-code evaluator statement and is smaller in scope than the arbitrary batch theorem, but it contains the core replay/recursive-evaluation correspondence.

## Axioms

`#print axioms AKLT.W.H3C034.main`:

```text
'AKLT.W.H3C034.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All are among the permitted axioms. The residual is a transparent `def`, not an axiom or theorem.

## Build

- `lake build AKLT.W.H3C034.Main` — succeeded; target reported 5.9 s, command wall time 15.3 s.

## Open issue

`AKLT.W.H3C034.PrefixStemSoundResidual` is not proved. Its proof must connect `replayPrefix` and `prefixDFS` to the exact decoded-word semantics, covering early target hits, surviving length-12 endpoints, endpoint lookup binding, exact short values and chronological ordering. The suggested `PrefixReplaySoundLeaf`, `PrefixReplayCompleteLeaf`, `PrefixStepLeaf`, `ShortValueLeaf`, `LastWindowCodeLeaf`, and `EndpointBoxLeaf` are frozen `Prop` definitions in the imported interface, not available theorems, and were not assumed.

The instruction to make the first attempt with a different cheaper model could not be carried out in this single-agent turn: the brief also prohibits sub-agents, and no model-switch control is exposed here. No forbidden Lean construct was added.

## ORCH-SUMMARY

- Delivered `Main.lean` and this report; `lake build AKLT.W.H3C034.Main` succeeds.
- `AKLT.W.H3C034.main` proves the batch leaf from `AKLT.W.H3C034.PrefixStemSoundResidual`.
- The unconditional requested theorem remains open; the residual is unproved and contains per-stem semantic evaluation.
- Batch additivity, stem-`ok` extraction, and semantic list-sum reduction are proved.
- Axioms printed for `main`: `propext`, `Classical.choice`, `Quot.sound` only.
- Suggested neighboring leaf Props were not assumed or proved.
- Preliminary cheaper-model attempt was unavailable under the single-agent/no-model-switch setup; no sub-agents were used.
- Orchestrator should pass on the stem residual for proof, or choose a later continuation for the full leaf.
