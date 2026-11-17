STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1M040/AKLT/W/H1M040/Main.lean)
- Report: `/home/ubuntu/aklt/reports/LW/H1M040/report.md`

## Exported declaration

`AKLT.W.H1M040.main : AKLT.Blueprint.H1.PositiveSpectrumStatement`

The proof equips `S` with its inherited norm and inner product, restricts `O` to `S`, and applies the finite-dimensional orthonormal eigenbasis theorem. Positivity implies positive real parts by testing each ambient eigenvector witness. Conversely, each restricted basis eigenvector gives an ambient `eigenvaluesOn` witness, and the quadratic form is the sum of the eigenvalues weighted by squared coordinate norms. This also handles `S = ⊥`, where positivity is vacuous.

Paper context read: `app-local-operator.tex`, Lemma `l:sector` (lines 472–555). Its final spectral-theorem argument corresponds to this leaf.

## Axioms

`#print axioms AKLT.W.H1M040.main`:

```text
'AKLT.W.H1M040.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are all permitted axioms for this task.

## Build

- `lake build AKLT.W.H1M040.Main` — succeeded; 18.1 s wall time (the Lean target reported 8.5 s).
- Axiom inspection: `lake env lean /tmp/H1M040Axioms.lean` — succeeded; 7.8 s.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.H1M040.main` with the exact requested type in `AKLT/W/H1M040/Main.lean`.
- The finite-dimensional spectral argument proves both directions, including the zero subspace case.
- Build succeeded with `lake build AKLT.W.H1M040.Main`.
- Axioms are `[propext, Classical.choice, Quot.sound]`; all are permitted.
- No residual statements, deviations, or open issues.
