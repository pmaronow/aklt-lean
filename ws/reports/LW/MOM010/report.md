STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_MOM010/AKLT/W/MOM010/Main.lean`
- `/home/ubuntu/aklt/reports/LW/MOM010/report.md`

## Exported declaration

`AKLT.W.MOM010.main : AKLT.Blueprint.Mom.PolynomialExpansionStatement`

The proof rewrites polynomial evaluation as the finite sum over `p.support`, factors the monomial exponent product over `Fin n × Fin 3` into the per-site `mono` products, distributes the configuration weight through the support sum, commutes the finite sums, and factors each coefficient outside the product quadrature.

## Axioms

`#print axioms AKLT.W.MOM010.main`:

```text
'AKLT.W.MOM010.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.MOM010.Main`
- Result: success
- Elapsed time: 12.98 s total; Lake reported 5.0 s for the module build.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.MOM010.main` with the exact requested type in `AKLT/W/MOM010/Main.lean`.
- The requested target built successfully with `lake build AKLT.W.MOM010.Main`.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- No additional helper files or changes to existing project files.
- No open proof issues or deviations.
