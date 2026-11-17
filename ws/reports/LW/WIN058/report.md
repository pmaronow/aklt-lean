STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_WIN058/AKLT/W/WIN058/Main.lean`

## Exported declaration

`AKLT.W.WIN058.main : AKLT.Blueprint.Win.PairDifferenceStatement`

The proof expands `pairSum` as half the ordered double sum, uses linearity of the normalized finite means, removes the diagonal, and bounds each remaining inner sum over `V.erase v`. The resulting coefficient is `|V|(|V|−1)/2`, at most six for `|V|=4` and at most three otherwise.

## Axioms

`#print axioms AKLT.W.WIN058.main`:

```text
'AKLT.W.WIN058.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.WIN058.Main` — succeeded; 9.3 seconds wall time (Lake reported 3.0 seconds for the module).
- `lake env lean /tmp/WIN058Axioms.lean` — succeeded; printed the axiom list above.

## Open issues

None.

## ORCH-SUMMARY

- Delivered the exact requested theorem in `AKLT/W/WIN058/Main.lean`.
- The requested Lake build succeeded.
- The theorem uses only the permitted classical and quotient axioms.
- No residual statements or deviations remain.
