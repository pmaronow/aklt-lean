STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_H3M010/AKLT/W/H3M010/Main.lean`
- `/home/ubuntu/aklt/reports/LW/H3M010/report.md`

## Exported declaration

- `AKLT.W.H3M010.main : AKLT.Blueprint.H3.SuffixWindowLabelsStatement`

The proof identifies every remembered letter with the corresponding whole-word letter, proves a translated-vertex identity for the ten-step window, and uses it to show that every remembered departure from the current vertex is also a true earlier departure. The arrival and successor labels then follow from the window indexing; if there is no true revisit, the remembered kind is the actual straight/turn kind.

## Axioms

`#print axioms AKLT.W.H3M010.main` reports:

```text
'AKLT.W.H3M010.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.H3M010.Main` — succeeded; Lake reported the new module built in 7.5 s (the final invocation took 19.6 s wall time, including Lake startup).
- `lake env lean /tmp/H3M010Axioms.lean` — succeeded and confirmed the declaration and axiom list.

## Open issues

None. The supplied `IsTrail` premise is not needed by this label identity proof.

## ORCH-SUMMARY

- Delivered `AKLT.W.H3M010.main` with the exact requested type in `AKLT/W/H3M010/Main.lean`.
- `lake build AKLT.W.H3M010.Main` succeeds.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- No residual statements, limitations, or deviations; the `IsTrail` hypothesis is unused.
