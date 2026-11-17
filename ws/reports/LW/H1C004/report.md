STATUS: PROVED FROM DEPS

## Files

- `/home/ubuntu/aklt/wt/LW_H1C004/AKLT/W/H1C004/Main.lean`
- `/home/ubuntu/aklt/reports/LW/H1C004/report.md`

## Exported declaration

`AKLT.W.H1C004.main : AKLT.Cert.H1.Production.TopLeaves.sylvester`

The real-valued criterion is proved by induction on the matrix dimension. In the inductive step, the matrix is split into its leading block and last coordinate; Mathlib's Schur complement characterization of positive semidefiniteness and block determinant identity give the result. The base case handles `Fin 0`. The integer statement follows by casting each leading determinant to `ℝ` and using preservation of determinants under ring homomorphisms.

## Axioms

`#print axioms AKLT.W.H1C004.main`:

```text
'AKLT.W.H1C004.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.H1C004.Main` — succeeded; first build completed in 11.54 s, final rebuild in 6.4 s.
- `lake env lean /tmp/H1C004Axioms.lean` — succeeded; printed the axiom list above.

The build emitted linter warnings for the local `letI` and inherited dependency warnings; no errors. The independent con-ron/NanoDa recheck has not been run here.

## Open issues

No proof gaps remain. The independent checker can perform its required downstream recheck.

## ORCH-SUMMARY

- Delivered `AKLT.W.H1C004.main` at the exact requested name and type in `Main.lean`.
- Proved the real symmetric Sylvester criterion by induction, including dimension zero, then specialized it to integer matrices via determinant casting.
- Theorem axioms are exactly `[propext, Classical.choice, Quot.sound]`.
- `lake build AKLT.W.H1C004.Main` succeeded; the independent con-ron/NanoDa recheck remains downstream.
- Only new source file is `AKLT/W/H1C004/Main.lean`; no existing source files were changed.
