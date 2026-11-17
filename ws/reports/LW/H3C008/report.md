STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H3C008/AKLT/W/H3C008/Main.lean)

## Exported declaration

`AKLT.W.H3C008.main : CertData.H3.Bridge.RevisitLeaf`

The proof uses `WalkRepresents` to rewrite `s.pos` as the final word vertex and `s.departed` as the reverse list of vertices at indices in `Fin n`. Simplification reduces the two sides to existence of an earlier matching vertex; the remaining proof converts between `Fin n` and `Finset.range n`. No certificate is normalized or evaluated.

## Axioms

`#print axioms AKLT.W.H3C008.main`:

```text
'AKLT.W.H3C008.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the allowed axioms listed in the brief.

## Build

- Command: `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.H3C008.Main`
- Result: successful, `Built AKLT.W.H3C008.Main`; target Lean compilation took 3.9 seconds (8.4 seconds total command time).

## Open issues and limitations

The brief required the first attempt to use a different, cheaper model. This runtime did not expose a way to switch the active model, and the task rules prohibit sub-agents, so that process requirement could not be met. The proof itself is complete and compiled in the assigned runtime.

## ORCH-SUMMARY

- Delivered `AKLT.W.H3C008.main : CertData.H3.Bridge.RevisitLeaf` in `AKLT/W/H3C008/Main.lean`.
- The proposition follows from the `WalkRepresents` list and position equalities and finite-index membership.
- Build succeeded with `lake build AKLT.W.H3C008.Main`; target compilation: 3.9 s; total command: 8.4 s.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- Limitation: first-attempt cheaper-model requirement could not be met because model switching was unavailable; sub-agents were prohibited.
- No mathematical proof gaps remain; orchestrator may record the process deviation.
