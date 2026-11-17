STATUS: PROVED

## Files

- `AKLT/W/WIN019/Main.lean`
- `/home/ubuntu/aklt/reports/LW/WIN019/report.md`

## Exported declaration

`AKLT.W.WIN019.main : AKLT.Blueprint.Win.CutEdgesNonemptyStatement`

The proof takes a site of maximal first coordinate in the nonempty finite set `A`. Its east neighbour has strictly larger first coordinate, so it is outside `A`; coordinate bounds show that it lies in the radius-one `starBall`. The resulting edge belongs to `cutEdges A`.

## Axioms

`#print axioms AKLT.W.WIN019.main` reports:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.WIN019.Main`
- Result: success; module build reported 5.2 seconds (15.8 seconds wall time for the command).

## Open issues

None.

## ORCH-SUMMARY

- Delivered the exact requested theorem in `AKLT/W/WIN019/Main.lean`.
- The theorem proves `AKLT.Blueprint.Win.CutEdgesNonemptyStatement`.
- Build: `lake build AKLT.W.WIN019.Main` succeeded.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- No helper files or existing project files were changed.
- No open issues.
