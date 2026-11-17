STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_GAP058/AKLT/W/GAP058/Main.lean)

## Exported declaration

- `AKLT.W.GAP058.main : AKLT.Blueprint.Gap.StoppedHammingConversionStatement`

The proof instantiates the stopped estimate at `h = n` and uses the radius identity to obtain its disagreement bound on the target far-site set. A local finite-sum lemma bounds the expected Hamming cost of that same coupling by the complement size plus the volume times disagreement. The assumed bounds `0 ≤ d ≤ p * α^(16*l) ≤ 1` give the natural-power comparison from `(1 - p * α^(16*l))^(n - 3)` to `(1 - d)^(n - 3)`. The two cardinality bounds finish the estimate.

## Axioms

Output of `#print axioms AKLT.W.GAP058.main`:

```text
'AKLT.W.GAP058.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.GAP058.Main`
- Result: successful; 10.36 seconds wall time (Lean module reported 5.6 seconds).
- A separate `lake env lean /tmp/GAP058Axioms.lean` check confirmed the axiom list above.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/GAP058/Main.lean` with the exact requested theorem `AKLT.W.GAP058.main`.
- The module compiles with `lake build AKLT.W.GAP058.Main`.
- The theorem uses only `[propext, Classical.choice, Quot.sound]`.
- The same stopped full-law coupling is retained through localization and the final Hamming bound.
- No residual statements, false-premise issues, or deviations remain.
