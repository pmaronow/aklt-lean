STATUS: PROVED

## Files

- `AKLT/W/H1C022/Main.lean`
- `/home/ubuntu/aklt/reports/LW/H1C022/report.md`

## Exported declaration

`AKLT.W.H1C022.main : AKLT.Cert.H1.Production.Leaves.sectorLinearity`

The proof establishes coefficient scaling for `rationalOperatorEntry` using `MvPolynomial.coeff_C_mul`, then distributes the scalar through the two finite sector sums. The polynomial scalar multiplies the complete polynomial, as required by the statement. This corresponds to the linearity of the Pauli expansion in paper label `d:Pauli`.

## Axioms

`#print axioms AKLT.W.H1C022.main`:

```text
'AKLT.W.H1C022.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.H1C022.Main` — succeeded; target compile reported 8.7 s (about 16 s wall time for the command including project replay).
- `lake env lean /tmp/H1C022Axioms.lean` — succeeded and printed the axiom list above.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.H1C022.main` with the requested exact type.
- Proof reduces the leaf to polynomial coefficient scaling and finite sum distributivity.
- `lake build AKLT.W.H1C022.Main` succeeds.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- No helper files or residual statements; no open issues.
