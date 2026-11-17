STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_Q037/AKLT/W/Q037/Main.lean)

## Exported declaration

- `AKLT.W.Q037.main : AKLT.Blueprint.Q.StarCasimirChartStatement`

All chart construction and transport helper declarations are private to the leaf module.

## Axioms

`#print axioms AKLT.W.Q037.main`:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.Q037.Main` — successful; module build 8.0 s (13.1 s wall time).

## Proof outline and open issues

The chart uses the center/east/west/north/south site map. Its injectivity uses only the side length bound `3 ≤ L,N`, including the distinct east and west sites at period three. The remaining sites are split into spectator configurations and enumerated by `Fin n`. Reindexing the Hilbert coordinates gives an isometric equivalence. The proof transports each one-site matrix on the four Casimir bonds, then transports sums, scalar multiples, and compositions to obtain the requested Casimir identities. No global coloring or nonincident bond information is used.

Open issues: none.

## ORCH-SUMMARY

- Delivered `AKLT.W.Q037.main` with the requested type.
- Added only `AKLT/W/Q037/Main.lean`; report is this file.
- Build passed with `lake build AKLT.W.Q037.Main`.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- No remaining work or limitations.
