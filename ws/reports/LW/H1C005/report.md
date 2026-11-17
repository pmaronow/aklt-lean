STATUS: PROVED

# H1C005 — prove one blueprint leaf

Paper label: `l:integercheck`.

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1C005/AKLT/W/H1C005/Main.lean)
- [report.md](/home/ubuntu/aklt/reports/LW/H1C005/report.md)

## Exported declaration

```lean
theorem AKLT.W.H1C005.main :
  AKLT.Cert.H1.Production.TopLeaves.bareiss
```

The theorem proves the frozen statement as given. All determinant, indexing, Schur-complement, and induction helpers are private to `Main.lean`.

## Proof outline

The induction invariant identifies each trailing Bareiss entry at stage `j` with the bordered leading minor of order `j + 1`, and identifies the saved denominator with the leading minor of order `j`. The transition follows from Desnanot–Jacobi. That identity is proved over `ℚ` by expressing the bordered minors as Schur complements of the leading block and applying the `2 × 2` determinant formula. The previous-pivot hypotheses supply the nonzero determinant needed to invert the leading block. The resulting integer product identity establishes exact divisibility before `Int.ediv_eq_of_eq_mul_left` is used for the recurrence.

## Axioms

`#print axioms AKLT.W.H1C005.main`:

```text
'AKLT.W.H1C005.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the permitted foundational axioms.

## Build

Command: `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.H1C005.Main`

Result: successful. The command completed in about 18 seconds; the target module reported 8.8 seconds. The build replayed existing project dependencies and built the requested module.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.H1C005.main` at the exact requested type.
- Proved the Bareiss minor invariant and exact divisibility by induction.
- Proved the required Desnanot–Jacobi identity through rational Schur complements.
- `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.
- `lake build AKLT.W.H1C005.Main` succeeds.
- No residual statements or deviations remain.
