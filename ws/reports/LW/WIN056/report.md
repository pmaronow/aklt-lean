STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_WIN056/AKLT/W/WIN056/Main.lean`

## Exported declaration

- `AKLT.W.WIN056.main : AKLT.Blueprint.Win.PolynomialLowerStatement`

The proof unfolds `removalPolynomial` and finite `expectation`, using the probability mass sum to evaluate the constant term. It splits on `V.card = 4`. In the four-site case the supplied pair and quartic bounds give `1 - 6/25 - 1/5 = 14/25`. Otherwise, `V.card ≤ 4` implies `V.card ≤ 3`, and the pair bound gives `1 - 9/50 = 41/50`. The integrands `pairSum` and `quartic` require no further expansion because their expectation bounds are hypotheses of the statement.

## Axioms

`#print axioms AKLT.W.WIN056.main`:

```text
'AKLT.W.WIN056.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.WIN056.Main`
- Result: successful; module build reported 4.6 s (full Lake invocation 9.4 s).

## Open issues

None.

## ORCH-SUMMARY

- Delivered the exact requested theorem in `AKLT/W/WIN056/Main.lean`.
- The leaf compiles with `lake build AKLT.W.WIN056.Main`.
- `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.
- No frozen statement or existing project file was changed.
- No open issues or deviations.
