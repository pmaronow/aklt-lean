STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1M044/AKLT/W/H1M044/Main.lean)

## Exported declaration

- `AKLT.W.H1M044.main : AKLT.Blueprint.H1.InversionCovarianceStatement`

The proof first establishes that evaluating `invertPolynomial I p` at `u` is
the same as evaluating `p` at `invertVectors I u`. It then uses the linearity
of matrix-vector multiplication to commute selected sign changes through any
orthogonal matrix, and applies the given invariance of `p`.

## Axioms

Output of `#print axioms AKLT.W.H1M044.main`:

```text
'AKLT.W.H1M044.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the permitted Lean axioms listed in the task.

## Build

- Command: `lake build AKLT.W.H1M044.Main`
- Result: successful; target module build reported 3.7 seconds (command wall time 8.8 seconds).

## Open issues

None.

## ORCH-SUMMARY

- Delivered the requested theorem with the exact namespace, name, and type.
- Proved it directly from `OrthogonalInvariant` using polynomial evaluation compatibility and linearity of `Matrix.mulVec`.
- The module builds successfully.
- Axioms: `propext`, `Classical.choice`, and `Quot.sound` only.
- No open issues or deviations.
