STATUS: PROVED

## Files

- `AKLT/W/Q002/Main.lean`

## Exported declaration

- `AKLT.W.Q002.main : AKLT.Blueprint.Q.OneSiteMomentEncodingStatement`

The witness is `MvPolynomial.rename (fun i => (0, i)) p`. Its separate degree bound follows because the only site coordinate is `0`, so the sum of its three exponents is the monomial's total degree. The one-site functional is reindexed from functions `Fin 1 → SpinLetter` to `SpinLetter`; the `none` atom has `U` weight zero and every `some a` atom has weight `1/12`. The identity and rotated evaluation formulas both follow from `MvPolynomial.eval_rename`, with no rotation invariance assumption.

## Axioms

`#print axioms AKLT.W.Q002.main`:

```text
'AKLT.W.Q002.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.Q002.Main`
- Result: successful.
- Lean module compile time: 5.0 s; command wall time: approximately 15.5 s.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/Q002/Main.lean` and proved the exact requested declaration `AKLT.W.Q002.main`.
- The proof uses the one-site variable rename, `Fin 1` functional reindexing, and direct polynomial evaluation under rename.
- `lake build AKLT.W.Q002.Main` succeeds; exported theorem axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements, deviations, or open issues.
