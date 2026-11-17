STATUS: PROVED

## Files

- `AKLT/W/H3M035/Main.lean`
- `/home/ubuntu/aklt/reports/LW/H3M035/report.md`

## Exported declaration

- `AKLT.W.H3M035.main : AKLT.Blueprint.H3.StoppedQuotientIntertwiningStatementV2`

The proof compares one stopped-operator step on valid raw states. `MemoryQuotient.Correct` supplies matching allowed directions, kinds, quotient successors, and arrivals on non-revisit edges. On revisit edges, the stated arrival-independence of the weight gives coefficient equality. The explicit raw-successor closure carries validity through the induction. The terminal tests and zero-step rewards use their respective pullback premises. The final finite sums are equal term by term. The extra premise that quotient rewards vanish off the stopping set is not needed for this equality.

Private helper declarations in the file establish the one-step pullback and the iterate pullback; no residual propositions or assumptions were introduced.

## Axioms

`#print axioms AKLT.W.H3M035.main`:

```text
[propext, Classical.choice, Quot.sound]
```

These are the allowed axioms. No `sorryAx` occurs.

## Build

Command: `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.H3M035.Main`

Result: successful. Final build elapsed time was 16.03 s (the module itself took 6.0 s; dependencies were already built).

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/H3M035/Main.lean` with `AKLT.W.H3M035.main` at the exact requested type.
- The finite-sum equality is proved by valid-state one-step pullback, iteration, and summation.
- `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Build succeeded with `lake build AKLT.W.H3M035.Main`.
- No residual obligations or deviations remain.
