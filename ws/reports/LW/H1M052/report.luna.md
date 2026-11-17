STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1M052/AKLT/W/H1M052/Main.lean)

## Declarations

- `AKLT.W.H1M052.RawDifferencePairExpansionResidual : Prop` — the concrete raw current-minus-next finite-sum `PairExpansion` obligation, retaining the ico unit-norm premise and quantifying over a covered pattern, a group inversion, a pair group, and rational `c`. It removes the supplied Pauli-realization equalities and exposes the finite-spin operator sum directly.
- `AKLT.W.H1M052.pauliOperator_invert_difference` — proved linearity of the Pauli operator under inversion of a polynomial difference.
- `AKLT.W.H1M052.main_of_rawDifferencePairExpansion` — proves `AKLT.Blueprint.H1.PairExpansionFromRealizationStatement` assuming the explicit residual above, by rewriting the difference operator and applying the two realization equalities.

The requested exported theorem `AKLT.W.H1M052.main` is not proved or declared in this partial delivery.

## Axioms

`#print axioms` output for both proved theorems:

```text
'AKLT.W.H1M052.pauliOperator_invert_difference' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.main_of_rawDifferencePairExpansion' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.H1M052.Main` — succeeded; final module build reported 7.8 s.
- Axioms checked with `PATH="$HOME/.elan/bin:$PATH" lake env lean /tmp/H1M052Axioms.lean`.

## Open issue

`RawDifferencePairExpansionResidual` remains unproved. Its proof must factor the two equal-sign slot factors in each raw Pauli summand, show the remaining operator commutes with pair symmetries, handle the zero-weight `none` atom at U sites, and assemble the finite sum while joining current and next with coefficient `c`. These are precisely the missing steps; no falsehood or missing hypothesis was found.

## ORCH-SUMMARY

- Delivered `AKLT/W/H1M052/Main.lean`; it compiles.
- Proved `pauliOperator_invert_difference` and the conditional bridge `main_of_rawDifferencePairExpansion`.
- Open exact declaration: `AKLT.W.H1M052.RawDifferencePairExpansionResidual`.
- The required theorem `AKLT.W.H1M052.main` is not yet established; status is PARTIAL.
- The unresolved work is summand pair factorization, commutation of auxiliary factors, zero-weight U-atom removal, and finite-sum/difference assembly.
- Exported proved theorems use only `[propext, Classical.choice, Quot.sound]`.
