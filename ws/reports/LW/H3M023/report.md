STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_H3M023/AKLT/W/H3M023/Main.lean`

## Exported declaration

- `AKLT.W.H3M023.main : AKLT.Blueprint.H3.ReflectionGeometryStatement`

The proof establishes the reflected vertex formula by additivity of `reflectSite` and its action on compass steps. It then transports trail bonds through the injective finite-set image, preserves departure counts by identifying the reflected vertex filters, and transfers the endpoint, avoidance, incoming reversal, straightness, revisit, and first-direction conditions.

## Axiom audit

Output of `#print axioms AKLT.W.H3M023.main`:

```text
'AKLT.W.H3M023.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the permitted standard axioms.

## Build

- Command: `lake build AKLT.W.H3M023.Main`
- Result: successful; target module compiled in 5.6 seconds (Lake reported 8961/8961 build jobs complete).

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/H3M023/Main.lean` with `AKLT.W.H3M023.main` at the required type.
- Status: proved; `lake build AKLT.W.H3M023.Main` succeeds.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- No residual statements, deviations, or open issues.
