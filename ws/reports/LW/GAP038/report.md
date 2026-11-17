STATUS: PROVED

Files:
- `/home/ubuntu/aklt/wt/LW_GAP038/AKLT/W/GAP038/Main.lean`

Exported declaration:
- `AKLT.W.GAP038.main : AKLT.Blueprint.Gap.TorusRangeTransferStatement`

The proof maps every torus neighbor of a site in a radius-`M` square to an offset in the radius-`M+1` square. Thus agreement on the full halo implies agreement on the four-neighbor set required by the local Markov hypothesis. A helper bridges the two marginal definitions, including their distinct `DecidableEq` instances.

`#print axioms AKLT.W.GAP038.main`:
```text
'AKLT.W.GAP038.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Build: `lake build AKLT.W.GAP038.Main` — succeeded; Main built in 5.6s (total 11.5s).

Open issues: none.

## ORCH-SUMMARY

- Delivered `AKLT.W.GAP038.main` with the exact requested statement in `AKLT/W/GAP038/Main.lean`.
- Proved from the statement's local conditional-law hypothesis and finite torus geometry.
- Build succeeded; theorem axioms are `[propext, Classical.choice, Quot.sound]`.
- No deviations or open issues.
