STATUS: PROVED

## Files

- `AKLT/W/GAP043/Main.lean`
- `/home/ubuntu/aklt/reports/LW/GAP043/report.md`

## Exported declaration

- `AKLT.W.GAP043.main : AKLT.Blueprint.Gap.ShellNestingStatement`

The proof unfolds the finite filters and reduces the first inclusion to monotonicity of the far-volume threshold. For the shell inclusion, `Int.sub_one_lt_floor` gives the lower floor bound, while `s ≥ 16` and `i + 1 ≤ j - 1` give the strict spacing margin. Integer inequalities are retained throughout, so negative indices require no natural subtraction.

## Axioms

`#print axioms AKLT.W.GAP043.main`:

```text
'AKLT.W.GAP043.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.GAP043.Main` — succeeded; module build reported 3.7 s (command wall time 8.9 s).
- A separate `lake env lean --stdin` import and axiom check succeeded (4.7 s command wall time).

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.GAP043.main` with the exact requested type in `AKLT/W/GAP043/Main.lean`.
- The requested Lake module build succeeded.
- The theorem uses only the permitted axioms `propext`, `Classical.choice`, and `Quot.sound`.
- No existing files were modified; no helper files or residual statements remain.
- No open issues or deviations; no orchestrator decision is needed.
