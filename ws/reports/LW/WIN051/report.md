STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_WIN051/AKLT/W/WIN051/Main.lean`
- `/home/ubuntu/aklt/reports/LW/WIN051/report.md`

## Exported declaration

- `AKLT.W.WIN051.main : AKLT.Blueprint.Win.SurvivorGeometryStatement`

The proof establishes the four-neighbour geometry directly: depth at least three places each neighbour in the original volume and gives each surviving neighbour depth at least two; the four compass neighbours are distinct and pairwise at distance two; removing any adjacent site leaves at most three survivors.

## Axioms

`#print axioms AKLT.W.WIN051.main`:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

- `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.WIN051.Main` — succeeded, 12.01 seconds real time (8955 jobs replayed).
- `PATH="$HOME/.elan/bin:$PATH" lake env lean AKLT/W/WIN051/Main.lean` — succeeded.

## Open issues

None.

## ORCH-SUMMARY

- Delivered the requested theorem at the exact name and type in `AKLT/W/WIN051/Main.lean`.
- The theorem builds successfully with the requested Lake target.
- Axioms are limited to `propext`, `Classical.choice`, and `Quot.sound`.
- No statement or existing project file was edited; no residual statements or open issues remain.
