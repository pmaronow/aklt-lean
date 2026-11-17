STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC023/AKLT/W/REC023/Main.lean)

## Exported declaration

- `AKLT.W.REC023.main : AKLT.Blueprint.Rec.ReciprocalIntegralStatement`

The proof separates `x = y`, where the integrand and logarithmic mean reduce to the constant `x`, from `x ≠ y`. In the latter case it proves positivity of the affine denominator on `[0,1]`, applies the fundamental theorem of calculus to its logarithm, and converts the endpoint expression to the reciprocal logarithmic mean. The logarithm difference is shown nonzero by strict monotonicity on positive reals before clearing denominators.

## Axioms

`#print axioms AKLT.W.REC023.main`:

```text
'AKLT.W.REC023.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.REC023.Main` — succeeded; Lake reported 5.5 seconds for the target build.
- `lake env lean AKLT/W/REC023/Main.lean` — succeeded and printed the axiom list. The combined build and Lean invocation took 17.0 seconds wall time.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.REC023.main` with the exact requested type in `AKLT/W/REC023/Main.lean`.
- Status is PROVED; the module builds successfully.
- Axioms are limited to `propext`, `Classical.choice`, and `Quot.sound`.
- No open proof obligations or deviations.
