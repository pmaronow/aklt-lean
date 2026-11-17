STATUS: PROVED

## Files

- `AKLT/W/REC073/Main.lean`

## Exported declaration

- `AKLT.W.REC073.main : AKLT.Blueprint.Rec.EnvelopeBoundsStatement`

The proof shows each normalized expectation of a spin dot product has absolute value at most 1: the support vectors have norm at most 1, each finite partition weight is nonnegative, and the observable is bounded pointwise by 1. Therefore each response is bounded by 2. The inserted zero and these response bounds give the nonnegative bounded supremum required by the statement.

## Axioms

`#print axioms AKLT.W.REC073.main`:

```text
'AKLT.W.REC073.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.REC073.Main`
- Result: success
- Lake-reported target compile time: 7.1 s

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.REC073.main` with the exact requested type in `AKLT/W/REC073/Main.lean`.
- The envelope bound follows from a direct finite-partition estimate and the supremum property.
- Build succeeded; exported theorem axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No helpers, assumptions, or deviations remain open.
