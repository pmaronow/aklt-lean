STATUS: PROVED

## Files

- `AKLT/W/Q035/Main.lean`

## Exported declarations

- `AKLT.W.Q035.main : AKLT.Blueprint.Q.StateCentreDegreeStatement`
- Helper: `AKLT.W.Q035.statePolynomial_eq_encode`

The proof rewrites `statePolynomial ψ` as `AKLT.Uniq.encode ψ`; then `encode_physical` gives weighted homogeneity of degree four at every site. The support hypothesis supplies the exponent to that homogeneity fact, and `siteWeight_degree` identifies its weight with `m (x, 0) + m (x, 1)`. The zero state is covered because the conclusion quantifies only over its (empty) support.

## Axioms

`#print axioms AKLT.W.Q035.main`:

```text
'AKLT.W.Q035.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.Q035.Main`
- Result: success; module build reported 5.4 s (11.8 s command wall time).

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.Q035.main` with the requested exact statement.
- The module builds successfully.
- Axioms are `[propext, Classical.choice, Quot.sound]`.
- No open proof obligations or deviations.
