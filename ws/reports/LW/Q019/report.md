STATUS: PROVED

## Files

- `AKLT/W/Q019/Main.lean`
- `/home/ubuntu/aklt/reports/LW/Q019/report.md`

## Exported declaration

`AKLT.W.Q019.main : AKLT.Blueprint.Q.SpectralKernelCoercivityStatement`

The proof uses the finite-dimensional orthonormal eigenbasis of the symmetric operator. Positivity makes each eigenvalue nonnegative. The residual after kernel projection is orthogonal to the full kernel, so coefficients at zero eigenvalues vanish; positive eigenvalues use the given lower bound. Symmetry identifies the residual quadratic form with the original one.

## Axioms

`#print axioms AKLT.W.Q019.main`:

```text
'AKLT.W.Q019.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `PATH="$HOME/.elan/bin:$PATH" lake env lean AKLT/W/Q019/Main.lean` — passed.
- `lake build AKLT.W.Q019.Main` — passed; 19.65 seconds elapsed, module reported 8.9 seconds.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/Q019/Main.lean` with the exact requested theorem name and type.
- The proof handles a kernel of arbitrary dimension and all nonnegative eigenvalues.
- Axiom footprint: `propext`, `Classical.choice`, `Quot.sound`.
- Requested Lake build succeeded.
- No residual statements or open issues.
