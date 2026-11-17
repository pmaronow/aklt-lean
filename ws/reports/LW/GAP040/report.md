STATUS: PROVED

## Files

- `AKLT/W/GAP040/Main.lean`
- No helper files.

## Exported declaration

`AKLT.W.GAP040.main : AKLT.Blueprint.Gap.FrameSpecRegularityStatement`

The proof takes the positivity and finite conditioning consistency assumptions directly. It converts a total assignment to its finite exterior boundary for the consistency clause, and proves boundary range one by showing every original leg ends at a site in the one-neighbourhood of the volume. The `planeWeight` products then agree factor by factor, so their normalized laws agree. The four-neighbour argument does not use a `Top` hypothesis.

## Axioms

`#print axioms AKLT.W.GAP040.main`:

```text
'AKLT.W.GAP040.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.GAP040.Main` — succeeded; Lake reported 8.8s for the module build (18.5s shell elapsed including startup).
- Axiom check: `lake env lean --stdin` with `import AKLT.W.GAP040.Main` and `#print axioms AKLT.W.GAP040.main` — succeeded.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/GAP040/Main.lean` with the exact requested theorem name and type.
- Proved positivity and finite-volume conditioning consistency from the supplied local inputs.
- Proved range one directly from the four-neighbour weight factors and normalized plane law.
- Build succeeded with `lake build AKLT.W.GAP040.Main`.
- Exported theorem axioms are `[propext, Classical.choice, Quot.sound]`.
- No open issues or deviations.
