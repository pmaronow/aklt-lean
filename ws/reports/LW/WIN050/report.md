STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_WIN050/AKLT/W/WIN050/Main.lean)
- [report.md](/home/ubuntu/aklt/reports/LW/WIN050/report.md)

## Exported declaration

`AKLT.W.WIN050.main : AKLT.Blueprint.Win.EnumerationStepsStatement`

The proof follows the frozen statement and the definitions of `RemovalEnumeration`, `removedPrefix`, `RemovalStep`, `boundaryDepth`, and `protectedSites` in `AKLT/Blueprint/Win/Defs.lean` and `AKLT/Defs/Geometry.lean`. Prefix membership is exactly membership in the image of the earlier indices. Injectivity gives the one-element prefix update and excludes the current site from its own prefix. The image equality gives the first and last prefix identities and shows all prefix sites lie in `X`; the depth bound excludes those sites from `protectedSites`. Finally, `previous` supplies the adjacent earlier site at every positive index.

## Axioms

`#print axioms AKLT.W.WIN050.main`:

```text
'AKLT.W.WIN050.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

Command:

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake build AKLT.W.WIN050.Main
```

Result: successful; `AKLT.W.WIN050.Main` built in 4.6 seconds. Lake reported build completion for the project (8955 jobs).

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.WIN050.main` with the requested exact type.
- The requested Lake target compiles successfully.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements or deviations.
- No orchestrator decision needed.
