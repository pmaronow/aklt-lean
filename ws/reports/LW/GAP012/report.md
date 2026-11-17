STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_GAP012/AKLT/W/GAP012/Main.lean`
- `/home/ubuntu/aklt/reports/LW/GAP012/report.md`

## Exported declarations

- `AKLT.W.GAP012.main : AKLT.Blueprint.Gap.FrameInteractionBoundsStatement`

The proof extracts adjacency from membership in `internalBonds`, applies proper colouring to get distinct frames on each edge, and uses the supplied per-edge bounds with finite product monotonicity. The product of the constant lower (upper) bound simplifies to the corresponding power of the internal bond count, including the empty-product case.

## Axioms

`#print axioms AKLT.W.GAP012.main` reports:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

Command: `lake build AKLT.W.GAP012.Main`

Result: successful. Incremental Lake invocation took 8.2 seconds; Lean reported 3.4 seconds for the module.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.GAP012.Main`; exported theorem is `AKLT.W.GAP012.main` with the requested statement type.
- Build succeeded and the theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.
- No open issues or deviations.
