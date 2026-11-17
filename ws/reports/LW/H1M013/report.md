STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1M013/AKLT/W/H1M013/Main.lean)
- This report: `/home/ubuntu/aklt/reports/LW/H1M013/report.md`

## Exported declaration

`AKLT.W.H1M013.main : AKLT.Blueprint.H1.MomentCovarianceTransferStatement`

The proof reindexes the finite internal support by `Fin V.card`, expands the local polynomial into monomials, applies the supplied `ProductMomentCovariance` to each transferred real polynomial, and transfers covariance through `contractSpins` using the supplied monomial moments. It uses the transpose rotation on spin coordinates and proves the finite product factorization locally. It does not use another blueprint leaf as a lemma or assume arbitrary-function invariance.

## Axioms

`#print axioms AKLT.W.H1M013.main`:

```text
'AKLT.W.H1M013.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.H1M013.Main` — passed; target module build reported 9.2 seconds (8954 jobs).
- `lake env lean /tmp/h1m013_axioms.lean` — passed; exact type and axiom check shown above.

## Open issues

None. The build emits non-fatal linter warnings about the explicit finite configuration instance and tactic style.

## ORCH-SUMMARY

- Delivered `AKLT.W.H1M013.main` with the requested closed statement type.
- Build passes: `lake build AKLT.W.H1M013.Main`.
- Axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`.
- Proof uses the two stated hypotheses and local finite-sum algebra; no other blueprint leaf theorem is used.
- No residual statements, deviations, or open issues.
