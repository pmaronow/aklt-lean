STATUS: PROVED

## Files

- `AKLT/W/H3C013/Main.lean`
- `/home/ubuntu/aklt/reports/LW/H3C013/report.md`

## Exported declaration

`AKLT.W.H3C013.main : CertData.H3.Bridge.RepresentativeBoundsLeaf`

The proof extracts each `representativeCheck` result from the successful full batch, then reads the checker’s first Boolean conjunct to obtain `G.representative a.val < 1048576`. It closes with `4^10 = 1048576`. It does not normalize or evaluate the full certificate.

## Axioms

Output of `#print axioms AKLT.W.H3C013.main`:

```text
'AKLT.W.H3C013.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `export PATH="$HOME/.elan/bin:$PATH"; lake build AKLT.W.H3C013.Main`
- Result: success; 16.7 seconds wall time (the target module job took 5.9 seconds).

## Open issues and limitations

- The brief required the first proof attempt to use a different, cheaper model, and also prohibited sub-agents. This session exposed no direct model-switch or model-inference tool, so that condition could not be met. The theorem was proved locally; no sub-agent was used.
- No open proof obligations remain.

## ORCH-SUMMARY

- Delivered `AKLT.W.H3C013.main` with the exact requested type in `AKLT/W/H3C013/Main.lean`.
- Proof follows the generic `representativeBatch` / `representativeCheck` definitions and the code bound `1048576 = 4^10`.
- Build succeeded with `lake build AKLT.W.H3C013.Main`.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- Limitation: first-attempt model requirement could not be fulfilled; no model-switch tool was available, and sub-agents were prohibited.
- Orchestrator action: none for the proof; note the model-selection deviation if enforcing that process requirement.
