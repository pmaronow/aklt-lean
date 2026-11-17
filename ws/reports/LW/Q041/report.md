STATUS: PROVED FROM DEPS

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_Q041/AKLT/W/Q041/Main.lean)
- This report: `/home/ubuntu/aklt/reports/LW/Q041/report.md`

## Exported declaration

`theorem AKLT.W.Q041.main : AKLT.Blueprint.Q.IncidentEvaluationStatement`

The proof uses the supplied factorization and independence hypotheses. It evaluates the state polynomial as the physical evaluation, reindexes the incident bond product over the four oriented neighbours, and retains the orientation sign for west and south factors. Independence at the centre makes the residual polynomial evaluation invariant under updates there; no residual isometry is used.

The only auxiliary proved dependency for the torus arithmetic is `AKLT.Challenge.small_natCast_ne_zero` from `AKLT/Challenge/Sanity.lean`.

## Axioms

`#print axioms AKLT.W.Q041.main`:

```text
'AKLT.W.Q041.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.Q041.Main` — succeeded; Lake reported 19s for the module (25.3s wall time).
- `PATH="$HOME/.elan/bin:$PATH" lake env lean /tmp/Q041Axioms.lean` — succeeded; printed the axiom list above.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/Q041/Main.lean` with `AKLT.W.Q041.main` at the required type.
- Proved the determinant product identity with all centre orientation signs retained.
- Used `independentAt` only to establish centre invariance of polynomial evaluation.
- No isometry or degree claim is made for the residual polynomial.
- Build command `lake build AKLT.W.Q041.Main` succeeded.
- Exported theorem axioms: `propext`, `Classical.choice`, `Quot.sound`.
- No residual statements or open issues.
