STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_Q031/AKLT/W/Q031/Main.lean)

## Exported declaration

- `AKLT.W.Q031.main : AKLT.Blueprint.Q.FourVariableDeterminantPrimeStatement`

The proof applies `MvPolynomial.irreducible_mul_X_add` with `X 3` as the polynomial variable. The coefficients `X 0` and `-(X 1 * X 2)` are relatively prime, and `X 3` does not occur in either coefficient. Irreducibility then gives primality in the multivariate polynomial UFD.

## Axiom audit

`#print axioms AKLT.W.Q031.main`:

```text
'AKLT.W.Q031.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.Q031.Main`
- Result: success; Lean reported `Built AKLT.W.Q031.Main (6.1s)`.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/Q031/Main.lean` with the requested theorem and exact type.
- Proof uses the primitive linear polynomial irreducibility lemma, then irreducible implies prime.
- Axiom audit contains only `propext`, `Classical.choice`, and `Quot.sound`.
- Build passed with `lake build AKLT.W.Q031.Main`.
- No open issues or deviations.
