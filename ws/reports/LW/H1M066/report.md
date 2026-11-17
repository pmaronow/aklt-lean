STATUS: PROVED

## Files

- `AKLT/W/H1M066/Main.lean`
- `/home/ubuntu/aklt/reports/LW/H1M066/report.md`

## Exported declaration

`AKLT.W.H1M066.main : AKLT.Blueprint.H1.RealDifferencePauliInterpolationStatementV2`.

Unfolded, this proves for all `π : PatternData`, `r : Representation`, `I : Finset (Fin 20)`, and `c : ℝ` that

```lean
pauliOperatorReal (reductionVectors π r)
    (invertPolynomialReal I (reducedDifferenceReal π r c)) =
  ((2 - 3 * c : ℝ) : ℂ) •
      pauliOperator (reductionVectors π r)
        (invertPolynomial I (reducedDifference π r (1 / 3))) +
    ((3 * c - 1 : ℝ) : ℂ) •
      pauliOperator (reductionVectors π r)
        (invertPolynomial I (reducedDifference π r (2 / 3)))
```

The proof establishes the real polynomial interpolation identity coefficientwise, then uses real linearity of inversion and the Pauli coefficient map. It also proves that rational coefficient embedding commutes with inversion and maps the real Pauli operator of an embedded rational polynomial to the rational Pauli operator.

## Axioms

`#print axioms AKLT.W.H1M066.main`:

```text
'AKLT.W.H1M066.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake env lean AKLT/W/H1M066/Main.lean` — succeeded in 9.6 s on the final source.
- `lake build AKLT.W.H1M066.Main` — succeeded; command wall time 16.0 s, module build reported 7.4 s.
- `lake env lean AKLT/W/H1M066/Axioms.lean` — succeeded in 6.4 s for the temporary axiom audit file, which was removed after inspection.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/H1M066/Main.lean` with `AKLT.W.H1M066.main` at the requested type.
- Proved from the frozen definitions and ring/matrix linearity; no other blueprint leaves were used.
- `lake build AKLT.W.H1M066.Main` succeeded.
- Axiom audit output is `[propext, Classical.choice, Quot.sound]`.
- Report saved at `/home/ubuntu/aklt/reports/LW/H1M066/report.md`.
- No known limitations or open declarations.
