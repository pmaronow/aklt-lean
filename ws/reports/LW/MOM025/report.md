STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_MOM025/AKLT/W/MOM025/Main.lean)

## Exported declaration

`AKLT.W.MOM025.main : AKLT.Blueprint.Mom.DepletedContractionStatement`

The proof applies `siteLawDecomposition`. At the zero vector, `localProduct a 0 = 1`, so the D denominator is `(3/5) * Uden + 2/5` and each D numerator is `(3/5)` times its U numerator. It obtains the coordinatewise mean relation `meanD = q * meanU`, where `q = ((3/5) * Uden) / Dden` lies in `(0,1)`, then expands `normSq (q * v) = q^2 * normSq v`.

## Axioms

Output of `#print axioms AKLT.W.MOM025.main`:

```text
'AKLT.W.MOM025.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.MOM025.Main` — successful; final run completed in 14.1 seconds wall time (module build reported 6.2 seconds).
- Axiom check: `lake env lean /tmp/mom025_axioms.lean` — successful.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.MOM025.main` with the exact requested type in `AKLT/W/MOM025/Main.lean`.
- Build succeeded with `lake build AKLT.W.MOM025.Main`.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- No residual statements, limitations, or deviations.
