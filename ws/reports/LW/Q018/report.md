STATUS: PROVED

## Files

- `AKLT/W/Q018/Main.lean`
- No helper files.

## Exported declaration

```lean
theorem AKLT.W.Q018.main :
    AKLT.Blueprint.Q.PositiveSpectralMinimumStatement
```

The proof enumerates the real eigenvalues supplied by the finite-dimensional spectral theorem. The positive eigenvalue set is finite and nonempty; it is bounded below by zero. A minimal element of that finite set is shown to equal its `sInf`, giving the positive attained minimum and the lower-bound property.

The quadratic-form nonnegativity premise is not needed for this statement: symmetry and the explicit positive eigenvalue witness suffice.

## Axioms

Output of `#print axioms AKLT.W.Q018.main`:

```text
'AKLT.W.Q018.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.Q018.Main`
- Result: successful; module build reported 5.5 s.
- Axiom check: `lake env lean /tmp/Q018Axioms.lean`, successful; 6.1 s.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.Q018.main` with the exact requested type in `AKLT/W/Q018/Main.lean`.
- Proof uses symmetric finite-dimensional spectral enumeration and a finite-set minimum; the positive witness ensures nonemptiness.
- The operator-positivity hypothesis is unused; no statement or directory deviations.
- Build succeeded with `lake build AKLT.W.Q018.Main`.
- Axiom dependencies are `[propext, Classical.choice, Quot.sound]`.
- No open issues.
