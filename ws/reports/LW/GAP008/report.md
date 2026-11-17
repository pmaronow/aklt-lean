STATUS: PROVED

## Files

- `AKLT/W/GAP008/Main.lean`
- `/home/ubuntu/aklt/reports/LW/GAP008/report.md`

## Exported declaration

- `AKLT.W.GAP008.main : AKLT.Blueprint.Gap.CommonMinorizationStatement`

The proof bounds each `|p x - q x|` by `(p x - t * ν x) + (q x - t * ν x)`, sums over the finite space, and uses the probability normalizations to obtain the bound `2 * (1 - t)`. It does not normalize residual laws, so the endpoints are covered by the same argument.

## Axioms

`#print axioms AKLT.W.GAP008.main`:

```text
'AKLT.W.GAP008.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.GAP008.Main` — successful; timed invocation completed in 4.97 seconds.

## Open issues

None.

## ORCH-SUMMARY

- Delivered the exact requested theorem in `AKLT/W/GAP008/Main.lean`.
- The proof derives the finite overlap bound directly from pointwise common minorization.
- `lake build AKLT.W.GAP008.Main` succeeds; exported axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No deviations or open issues.
