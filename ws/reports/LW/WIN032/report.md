STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_WIN032/AKLT/W/WIN032/Main.lean:1)
- No helper files.

## Exported declaration

`AKLT.W.WIN032.main : AKLT.Blueprint.Win.CoreConnectedStatement`

The proof derives the scale and seed-coordinate bounds from `CutSetup`, characterizes the core as the shell boundary clipped by the inner square, constructs a shell corner in that intersection, and joins each core site to the corner along one or two lattice side segments. It then proves the core lies in the taper using radial offset zero.

## Axioms

`#print axioms AKLT.W.WIN032.main`:

```text
'AKLT.W.WIN032.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.WIN032.Main` — succeeded; 13.2 seconds total, module build 7.4 seconds.
- A separate `lake env lean /tmp/win032_axioms.lean` check printed the axiom list above.
- Searched the delivered file for forbidden proof escapes and effects; none found.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/WIN032/Main.lean` and proved `AKLT.W.WIN032.main` with the exact requested type.
- The proof is self-contained apart from the frozen statement and its definitions imported from `AKLT.Blueprint.Win.NodesTaper`.
- Lake build succeeded; exported theorem axioms are `[propext, Classical.choice, Quot.sound]`.
- No residual statements, deviations, or open issues.
