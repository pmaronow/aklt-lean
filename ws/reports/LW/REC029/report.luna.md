STATUS: PARTIAL

## Files

- `AKLT/W/REC029/Main.lean`
- `/home/ubuntu/aklt/reports/LW/REC029/report.md`

## Delivered declarations

- `AKLT.W.REC029.Residual_1`: every permitted U/D site field list has a positive normalizer and effective mean with squared norm at most `(3/5)^2`.
- `AKLT.W.REC029.Residual_2`: every vector in that radius-`3/5` ball is the mean of three unit U fields with positive normalizer.
- `AKLT.W.REC029.affineFactor_identity`: for a nonzero normalizer, inserting `(1 + dot n v)` into a site functional multiplies the normalizer by `1 + dot (localMean s a) v`.
- `AKLT.W.REC029.main_of_residuals`: `Residual_1 → Residual_2 → AKLT.Blueprint.Rec.TipReplacementStatement`.

The requested unconditional `AKLT.W.REC029.main : AKLT.Blueprint.Rec.TipReplacementStatement` is not yet proved. The remaining work is to prove the two explicit residuals. `Residual_1` is the three-factor mean bound for up to three ball fields, including D status; `Residual_2` is the exact three-unit-field realization of every mean in the closed radius-`3/5` ball. These are the range and bound arguments from `l:35`.

## Axiom audit

`#print axioms AKLT.W.REC029.main_of_residuals` and
`#print axioms AKLT.W.REC029.affineFactor_identity` both report:

```text
[propext, Classical.choice, Quot.sound]
```

No forbidden axioms or placeholders are used in the delivered file.

## Build

Command: `export PATH="$HOME/.elan/bin:$PATH"; lake build AKLT.W.REC029.Main`

Result: successful. Initial full build: 13.27 s wall time, with 5.7 s reported for the module. Final cached replay: 4.94 s wall time.

## Open issues

- Prove `AKLT.W.REC029.Residual_1`.
- Prove `AKLT.W.REC029.Residual_2`.
- Then replace the conditional `main_of_residuals` with the exact requested unconditional theorem `AKLT.W.REC029.main`.

## ORCH-SUMMARY

- Delivered the compiled affine-factor identity and the conditional single-tip assembly.
- Exact residuals: `AKLT.W.REC029.Residual_1`, `AKLT.W.REC029.Residual_2`.
- The required unconditional theorem `AKLT.W.REC029.main` remains open.
- The conditional theorem's axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`.
- The Lake build completed successfully.
