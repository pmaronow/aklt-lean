STATUS: PROVED

## Files

- `AKLT/W/WIN005/Main.lean`
- No helper files.

## Exported declaration

`AKLT.W.WIN005.main : AKLT.Blueprint.Win.ExceptionalCountStatement`

The proof uses `Finset.card_le_one`: for any two exceptional indices in increasing order, localization gives close-corner witnesses. The assumed bound on the filtered corner set forces those corners to be equal. The two radial errors then imply that the radii differ by less than `2 * shellSpacing u / 3`, contradicting the assumed radius gap. The reverse order is handled by swapping the indices.

## Axioms

Output of `#print axioms AKLT.W.WIN005.main`:

```text
'AKLT.W.WIN005.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.WIN005.Main`
- Result: successful; Lean reported the module built in 6.3s (13.7s total command wall time).
- A separate `lake env lean /tmp/WIN005_axioms.lean` check printed the axiom output above and completed in 6.5s.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.WIN005.main` with the requested exact type.
- The new module builds successfully.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements, deviations, or open issues.
