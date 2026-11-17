STATUS: PROVED

## Files

- `AKLT/W/REC009/Main.lean`

## Exported declarations

- `AKLT.W.REC009.main : AKLT.Blueprint.Rec.CrudeLogEnclosureStatement`
- Private helper `atanh_crude`: for `0 < t < 1`, bounds `log ((1+t)/(1-t))` by the three displayed terms and its geometric remainder.

The proof uses Mathlib's logarithm power series. After separating its first two terms, each tail coefficient is bounded by `2/5`; summing the resulting geometric majorant gives `2*t^5/(5*(1-t^2))`. The rational substitution `t=(1-s)/(1+s)` converts this into the required reciprocal logarithmic mean inequality. The positive denominators follow from `0 < s < 1` and `0 < t < 1`.

## Axioms

`#print axioms AKLT.W.REC009.main`:

```text
'AKLT.W.REC009.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the permitted Lean axioms.

## Build

- `lake build AKLT.W.REC009.Main` — succeeded; the target module built in 7.3 s, total command time 13.2 s on the initial build.
- Rebuild after removing the temporary `#print axioms` command — succeeded, 6.7 s total (cached dependencies).

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/REC009/Main.lean` with the exact requested theorem name and type.
- Proved the enclosure from the logarithm series and an explicit geometric tail bound.
- `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.
- `lake build AKLT.W.REC009.Main` succeeds.
- No remaining proof obligations or deviations.
