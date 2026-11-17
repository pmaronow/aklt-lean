STATUS: PROVED

## Files

- `AKLT/W/Q040/Main.lean`
- `/home/ubuntu/aklt/reports/LW/Q040/report.md`

## Exported declaration

`AKLT.W.Q040.main : AKLT.Blueprint.Q.GroundProductWeightStatement`

The proof rewrites the supplied frame evaluation as the bond determinant product, applies multiplicativity of `Complex.normSq` over finite products, and substitutes the supplied edge modulus identities. Unfolding the three weights leaves the exact site factor `5 ^ Fintype.card (Site L N)` and edge factor `2 ^ Fintype.card (Bond L N)`; finite cardinality simplification closes the scalar identity. No torus probability identity is used.

## Axioms

`#print axioms AKLT.W.Q040.main`:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.Q040.Main` — passed, module build reported 6.0s.
- `lake env lean AKLT/W/Q040/Main.lean` — passed; printed the same axiom list.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/Q040/Main.lean` with the exact requested theorem name and type.
- The proof uses only the two hypotheses in the frozen statement and finite product/cardinality simplification.
- Exact factors `5^|sites|` and `2^|bonds|` are retained; each bond index appears once.
- Build passed with `lake build AKLT.W.Q040.Main`.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- No limitations or deviations; no open issues.
