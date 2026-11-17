STATUS: PROVED

## Files

- `AKLT/W/REC061/Main.lean`

## Exported declaration

- `AKLT.W.REC061.main : AKLT.Blueprint.Rec.KernelPositivityStatement`

## Proof

The length coefficient is a finite sum over direction words. Each summand is either zero or the product of a nonnegative trail base weight and an exposure sum. The exposure sum is nonnegative by induction on its ordering list: passage factors are positive and every response coefficient is nonnegative. The response coefficient is a finite sum of nonnegative pair coefficients (or zero).

For response pairs, membership in `powersetCard 2` gives cardinality two. The exact coefficient definition selects one of the positive rational alpha, beta, or beta-prime table entries, so it is positive.

All helper lemmas are private to the new module. No other blueprint leaf is used.

## Axioms

`#print axioms AKLT.W.REC061.main`:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.REC061.Main` — successful; module build reported 4.2 s (command wall time 10.4 s).

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/REC061/Main.lean` with the requested theorem and exact type.
- The theorem proves coefficient nonnegativity and response-pair cardinality/strict positivity directly from definitions.
- No other blueprint leaf lemmas, residual statements, or deviations were used.
- `#print axioms` output: `propext`, `Classical.choice`, `Quot.sound`.
- Build command: `lake build AKLT.W.REC061.Main`; successful.
- Open issues: none.
