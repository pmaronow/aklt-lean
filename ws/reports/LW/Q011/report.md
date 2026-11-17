STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_Q011/AKLT/W/Q011/Main.lean)

## Exported declarations

- `AKLT.W.Q011.realPartPolynomial` and `AKLT.W.Q011.imagPartPolynomial`: coefficientwise real and imaginary parts of a complex multivariate polynomial.
- `AKLT.W.Q011.realPartPolynomial_degree` and `AKLT.W.Q011.imagPartPolynomial_degree`: each part has total degree at most that of the original polynomial.
- `AKLT.W.Q011.ofReal_weightedSum`: real finite weighted sums commute with the real-to-complex embedding.
- `AKLT.W.Q011.eval_complex_eq_parts`: evaluation of a complex polynomial at real coordinates equals the evaluation of its real part plus `I` times the evaluation of its imaginary part.
- `AKLT.W.Q011.weighted_eval_parts` and `AKLT.W.Q011.complexMoment_parts`: the same decomposition for the frame weighted sum and the icosahedral moment, respectively.
- `AKLT.W.Q011.main : AKLT.Blueprint.Q.ComplexQuadratureStatement`.

## Axioms

`#print axioms AKLT.W.Q011.main`:

```text
'AKLT.W.Q011.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.Q011.Main` — passed; Lake wall time 10.0 s, Lean module build 5.1 s.
- Axioms checked with `lake env lean /tmp/Q011Axioms.lean` — passed; 5.3 s.

## Open issues

None. The proof applies the stated real quadrature identity separately to the two coefficient parts and recombines the resulting equalities. It assumes no positivity or normalization of the weights.

## ORCH-SUMMARY

- Delivered `AKLT.W.Q011.main` with the exact requested statement in `AKLT/W/Q011/Main.lean`.
- The complex result follows from real quadrature for the coefficientwise real and imaginary polynomials; both degree bounds are proved.
- Build passed; exported theorem axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements, limitations, or deviations.
