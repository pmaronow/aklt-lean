STATUS: PROVED FROM DEPS

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_MOM031/AKLT/W/MOM031/Main.lean)
- This report: `/home/ubuntu/aklt/reports/LW/MOM031/report.md`

## Exported declaration

`AKLT.W.MOM031.main : AKLT.Blueprint.Mom.SingleSiteQuadratureStatement`

The proof applies `MomentLaw` to the polynomial with exponent vector `m`, bounds its total degree by `∑ i, m i`, and identifies its evaluation with `mono m`. It then splits `s = .U` or `s = .D` and transfers the moment equality using the proved `siteLawDecomposition` theorem.

## Axiom audit

`#print axioms AKLT.W.MOM031.main`:

```text
'AKLT.W.MOM031.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.MOM031.Main` — succeeded; Lake reported `Built AKLT.W.MOM031.Main (5.0s)`.
- Axiom audit ran with `lake env lean` on a temporary audit file; it was removed after the audit.

## Open issues

None.

## ORCH-SUMMARY

- Delivered the exact requested theorem and type in `AKLT/W/MOM031/Main.lean`.
- The proof uses the supplied `MomentLaw` hypothesis and the proved `siteLawDecomposition` dependency.
- Build succeeded; axiom output is recorded above.
- No residual statements, deviations, or open issues.
