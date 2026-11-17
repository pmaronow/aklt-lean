STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_MOM017/AKLT/W/MOM017/Main.lean)

## Exported declaration

- `AKLT.W.MOM017.main : AKLT.Blueprint.Mom.FactorizedConditioningStatement`

The fibre is equivalent to `SpinLetter × SpinLetter`, with inverse given by updating the reference configuration at the two selected coordinates. Reindexing the finite sums gives the fibre mass and the joint and marginal event numerators. Positivity of normalized fibre mass implies positive unnormalized fibre mass, allowing cancellation of the common normalizer; the remaining identity follows from the rank-one factorization.

## Axioms

`#print axioms AKLT.W.MOM017.main`:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.MOM017.Main`
- Result: successful; module build time reported by Lake was 5.6 seconds.

## Open issues

None.

## ORCH-SUMMARY

- Delivered the requested theorem at the exact name and type in `AKLT/W/MOM017/Main.lean`.
- Build succeeds with `lake build AKLT.W.MOM017.Main`.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No deviations or remaining proof obligations.
