STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_GAP035/AKLT/W/GAP035/Main.lean)

## Exported declaration

- `AKLT.W.GAP035.main : AKLT.Blueprint.Gap.LiftBondStatement`

The proof characterizes plane adjacency by its four unit coordinate displacements. For torus bonds, it uses positive-direction bond indexing and the halo injectivity hypothesis to identify lifted endpoints. The same injectivity gives the required equivalence between membership in the reduced square image and membership in the plane square. Crossing bonds are handled in both orientations, with endpoint sets kept unordered.

## Axioms

Output of `#print axioms AKLT.W.GAP035.main`:

```text
'AKLT.W.GAP035.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.GAP035.Main` — succeeded; module build reported 9.3 s.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.GAP035.main` with the exact requested type in `AKLT/W/GAP035/Main.lean`.
- Proved internal bond correspondence, both crossing-bond orientations, and the halo image-membership equivalence.
- Build succeeded with only the standard axioms `[propext, Classical.choice, Quot.sound]`.
- No residual statements, limitations, or deviations.
- No orchestrator decision is needed.
