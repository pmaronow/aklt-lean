STATUS: PROVED

## Files

- `AKLT/W/H3C051/Main.lean`
- This report: `/home/ubuntu/aklt/reports/LW/H3C051/report.md`

## Exported declaration

- `AKLT.W.H3C051.main : CertData.H3.Bridge.UnmaskedDataLeaf`

The proof unfolds the packed graph accessors and uses the equalities in
`PackedGraph.Transcribed`. The representative, destination, and kind data
therefore reduce to the corresponding supplied table lanes. Small helper
lemmas identify the two lane definitions and direction-code definitions; the
edge index multiplication is commuted by `omega`.

## Axioms

`#print axioms AKLT.W.H3C051.main`:

```text
'AKLT.W.H3C051.main' depends on axioms: [propext, Quot.sound]
```

## Build

Command: `export PATH="$HOME/.elan/bin:$PATH"; lake build AKLT.W.H3C051.Main`

Result: successful. Lake reported `Built AKLT.W.H3C051.Main (5.9s)`; total
command time was about 11 seconds.

## Open issues and deviations

- No proof issues remain.
- The requested cheaper-model first attempt could not be selected through the
  active interface. The brief also prohibits sub-agents, so the proof was
  completed in the assigned session.

## ORCH-SUMMARY

- Delivered `AKLT/W/H3C051/Main.lean` and proved the exact requested theorem.
- Build command `lake build AKLT.W.H3C051.Main` succeeded.
- Axiom output: `[propext, Quot.sound]`.
- No open proof obligations.
- Limitation: no model-switch control was exposed; no sub-agent was used, per brief.
- Orchestrator action: none required.
