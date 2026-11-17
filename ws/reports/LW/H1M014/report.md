STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_H1M014/AKLT/W/H1M014/Main.lean`
- `/home/ubuntu/aklt/reports/LW/H1M014/report.md`

## Exported declaration

`AKLT.W.H1M014.main : AKLT.Blueprint.H1.ContractionAffineStatement`

Expanded, the theorem states that for every finite internal site set `V`, status function `s`, and local polynomial `p`, `LocalVectorAffine p` implies `VectorAffine (contractSpins V s p)`.

## Axioms

`#print axioms AKLT.W.H1M014.main`:

```text
'AKLT.W.H1M014.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.H1M014.Main`
- Result: success; module build reported 3.3 seconds.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.H1M014.main` with the requested type.
- The proof uses `MvPolynomial.support_sum` and `support_monomial_subset` to trace each output support exponent to an input support exponent.
- `Finsupp.comapDomain Sum.inr` preserves every external coordinate, hence each external token's summed degree.
- `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Build command `lake build AKLT.W.H1M014.Main` succeeds.
- No open issues or deviations.
