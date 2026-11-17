STATUS: PROVED

## Files

- `AKLT/W/H1M015/Main.lean`
- `/home/ubuntu/aklt/reports/LW/H1M015/report.md`

## Exported declaration

- `AKLT.W.H1M015.main : AKLT.Blueprint.H1.ContractionSupportStatement`

The proof uses `MvPolynomial.support_sum` to show that a support exponent in the contracted polynomial comes from a term indexed by an exponent in `p.support`. The term is a single monomial whose exponent is `Finsupp.comapDomain Sum.inr`, so each external coordinate `(j, k)` equals the corresponding input coordinate `m (.inr (j, k))`. The input support hypothesis makes that coordinate zero whenever `j ∉ J`.

## Axioms

`#print axioms AKLT.W.H1M015.main` output:

```text
'AKLT.W.H1M015.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.H1M015.Main`
- Result: successful
- Timing: 9.5 seconds wall time for the command; Lean reported 4.4 seconds for the module build.

## Open issues

None.

## ORCH-SUMMARY

- Delivered the exact requested theorem in `AKLT/W/H1M015/Main.lean`.
- The requested Lake build succeeded.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No helper files or existing project files were changed.
- No open issues or deviations.
