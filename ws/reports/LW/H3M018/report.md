STATUS: PROVED

## Files

- `AKLT/W/H3M018/Main.lean` — proof and private helper lemmas.

## Exported declaration

- `AKLT.W.H3M018.main : AKLT.Blueprint.H3.SuffixWordComparisonStatement`

The proof identifies the suffix fold with a backward four-phase recursion by finite sum commutation. It then inducts over the suffix indices, using the two supplied pointwise premises at each step to compare coefficients and update the quotient state. The closed-trail endpoint identifies the terminal stationary reward with `phaseTerminal`; append/take and vertex lemmas align the initial prefix state and suffix letters.

## Axioms

`#print axioms AKLT.W.H3M018.main`:

```text
'AKLT.W.H3M018.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.H3M018.Main` — successful, 9.9 seconds.
- Axiom check: `lake env lean /tmp/H3M018Axioms.lean` — successful, 9.0 seconds.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/H3M018/Main.lean` with `AKLT.W.H3M018.main` at the requested exact type.
- The requested module build succeeds.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements, deviations, or open issues.
