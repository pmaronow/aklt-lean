STATUS: PROVED

## Files

- `AKLT/W/Q046/Main.lean`
- `/home/ubuntu/aklt/reports/LW/Q046/report.md`

## Exported declaration

`AKLT.W.Q046.main : AKLT.Blueprint.Q.WeightedPolarizationStatement`

The proof establishes the scalar complex polarization identity termwise under the finite sum. Real weights commute through the conjugation in the first inner-product slot. It then applies the norm hypothesis to the four combinations `ψ + φ`, `ψ - φ`, `ψ - iφ`, and `ψ + iφ`, and closes with Mathlib's complex inner-product polarization identity. It does not require positivity or normalization of the weights.

## Axioms

`#print axioms AKLT.W.Q046.main`:

```text
'AKLT.W.Q046.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake env lean AKLT/W/Q046/Main.lean` — succeeded (standalone compile, about 8 seconds during development).
- `lake build AKLT.W.Q046.Main` — succeeded; Lake reported 5.2 seconds for the module, 11.554 seconds wall time for the command.
- `lake env lean --stdin` with an import of the module and `#print axioms AKLT.W.Q046.main` — succeeded.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.Q046.main` with the exact requested type in `AKLT/W/Q046/Main.lean`.
- Status: PROVED; the requested module build succeeded.
- The proof uses Mathlib's complex polarization identity after deriving its weighted finite-sum form.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No remaining declarations or decisions are open.
