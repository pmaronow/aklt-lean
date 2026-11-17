STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1M012/AKLT/W/H1M012/Main.lean)

## Exported declaration

- `AKLT.W.H1M012.main : AKLT.Blueprint.H1.MomentContractionStatement`

The proof expands each polynomial on its finite monomial support, separates the internal and external exponents, factors the finite spin sum over sites, and applies the supplied local moment identity to each internal monomial. `InternalAdmissible` supplies the omitted-site support condition and the per-site degree bound.

## Axioms

`#print axioms AKLT.W.H1M012.main` returned:

```text
'AKLT.W.H1M012.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.H1M012.Main` — succeeded; full target build reported 14.4 s wall time (7.6 s for the module). A final incremental build succeeded in 5.1 s.
- `lake env lean AKLT/W/H1M012/Main.lean` — succeeded.
- No tests were added or run.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/H1M012/Main.lean` with `AKLT.W.H1M012.main` proving the exact requested type.
- The finite monomial expansion, internal support restriction, sitewise moment factorization, and contraction evaluation are proved in private helpers in the same file.
- `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.
- The requested Lake build succeeds.
- No residual statements, deviations, or open issues remain.
