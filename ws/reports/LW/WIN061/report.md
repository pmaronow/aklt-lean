STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_WIN061/AKLT/W/WIN061/Main.lean)

## Exported declaration

`AKLT.W.WIN061.main : AKLT.Blueprint.Win.RemovalTelescopeStatement`

The proof telescopes the adjacent prefix log ratios over `Finset.range (e.last + 1)`, applies the triangle inequality to the resulting sum, and separates index zero from the remaining indices. The `Fin e.last` tail is empty when `e.last = 0`, so the singleton case follows from the seed bound. No enumeration fields beyond the supplied prefix endpoints and local bounds are needed.

## Axioms

`#print axioms AKLT.W.WIN061.main` reports:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.WIN061.Main`
- Result: successful.
- Latest build timing: Lean reported 14s for the module; shell timing was 19.918s real, 12.639s user, 4.815s system.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.WIN061.main` with the exact requested type.
- File: `AKLT/W/WIN061/Main.lean`.
- Build: `lake build AKLT.W.WIN061.Main` succeeded.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- Singleton case is included; no additional enumeration injectivity fact was needed.
- No residual statements or open issues.
