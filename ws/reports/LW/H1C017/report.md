STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1C017/AKLT/W/H1C017/Main.lean) proves the leaf.

## Exported declaration

- `AKLT.W.H1C017.main : AKLT.Cert.H1.Production.Leaves.signedPacking`

The proof writes the signed bias as the sum of half-base offsets using `Nat.geomSum_eq`. It shifts every bounded signed coefficient into the digit interval `[0, 2^width)`, proves natural mixed-radix quotient/remainder recovery by induction on the digit index, then translates that result back to `Int`. The signed interval is used with its stated inclusive lower and exclusive upper endpoints.

## Axiom audit

`#print axioms AKLT.W.H1C017.main`:

```text
'AKLT.W.H1C017.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the allowed axioms. No residual statements or additional helper files remain.

## Build

- Command: `time lake build AKLT.W.H1C017.Main`
- Result: successful; Lake reported `Built AKLT.W.H1C017.Main (6.2s)`.
- Wall time: 11.391s (`user` 12.539s, `sys` 3.170s).
- Lake replayed existing dependencies and emitted warnings in `AKLT.Gen.Gram.Theory` and `AKLT.Gen.Gram.Checker`; the new module built successfully.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.H1C017.main` with the exact requested type in `AKLT/W/H1C017/Main.lean`.
- Proves signed biased base-`2^width` digit recovery from finite geometric sums and quotient/remainder.
- Build succeeded with `lake build AKLT.W.H1C017.Main`.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- No residual statements or deviations; no orchestrator decision is needed.
