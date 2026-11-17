STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1M042/AKLT/W/H1M042/Main.lean)
- This report: `/home/ubuntu/aklt/reports/LW/H1M042/report.md`

## Exported declaration

`AKLT.W.H1M042.main : AKLT.Blueprint.H1.ReflectionParityStatement`

The proof specializes covariance to the explicit `reflectY` matrix, uses `MvPolynomial.funext` to identify the reflected real polynomial with the original, and compares the coefficient of `pauliExponent J a`. That coefficient is multiplied by `(-1) ^ pauliYCount J a`; oddness makes this factor `-1`, forcing the coefficient to vanish. `VectorAffine` and `SupportedVectors` are unused because covariance alone suffices for the coefficient argument.

## Axioms

`#print axioms AKLT.W.H1M042.main`:

```text
'AKLT.W.H1M042.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.H1M042.Main` — succeeded; clean module build took 7.1 s. A final incremental build also succeeded in 5.2 s.
- `lake env lean AKLT/W/H1M042/Main.lean` — used to print axioms; 7.4 s.

## Open issues

None.

## ORCH-SUMMARY

- Delivered the requested theorem `AKLT.W.H1M042.main` in `AKLT/W/H1M042/Main.lean`.
- The target builds successfully with the requested Lake command.
- Axioms are `[propext, Classical.choice, Quot.sound]`.
- The affine and support premises are not needed by this proof.
- No open issues or deviations.
