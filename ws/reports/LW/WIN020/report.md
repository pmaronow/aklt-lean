STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_WIN020/AKLT/W/WIN020/Main.lean): proves the leaf by filtering the finite crossing-edge set to the edges reachable from a chosen edge. A one-step `Linked` extension keeps the filtered set closed, and an unreachable edge is outside it.
- This report: `/home/ubuntu/aklt/reports/LW/WIN020/report.md`.

## Exported declaration

`AKLT.W.WIN020.main : AKLT.Blueprint.Win.LinkedSeparationStatement`

## Axioms

`#print axioms main`:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.WIN020.Main`
- Result: successful; Lake reported 5.4 seconds for the module (about 11 seconds wall time for the command).

## Open issues

None. No residual statements or deviations.

## ORCH-SUMMARY

- Delivered `AKLT/W/WIN020/Main.lean` with the requested theorem and exact type.
- Proof uses the finite `Linked`-reachable component of a selected crossing edge.
- `#print axioms`: `[propext, Classical.choice, Quot.sound]`.
- Build passed with `lake build AKLT.W.WIN020.Main`.
- Open issues: none; no orchestrator decision required.
