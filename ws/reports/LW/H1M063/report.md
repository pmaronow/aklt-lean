STATUS: PROVED

## Files

- `AKLT/W/H1M063/Main.lean`

## Exported declaration

- `AKLT.W.H1M063.main : AKLT.Blueprint.H1.DifferenceStructureStatementV2`

The proof establishes affine degree and vector support using the support inclusion for subtraction and multiplication by a constant polynomial. Orthogonal invariance follows from evaluation preserving subtraction and multiplication by `C c`.

## Axioms

`#print axioms AKLT.W.H1M063.main`:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.H1M063.Main`
- Result: successful; module build reported 6.2s.

## Open issues

None.

## ORCH-SUMMARY

Delivered `AKLT.W.H1M063.Main.main` with the exact requested type.
Build succeeds; axioms are `propext`, `Classical.choice`, and `Quot.sound`.
No residual statements, deviations, or open issues.
