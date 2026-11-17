STATUS: PROVED

## Files

- `AKLT/W/WIN073/Main.lean`
- `/home/ubuntu/aklt/reports/LW/WIN073/report.md`

## Exported declaration

```lean
theorem AKLT.W.WIN073.main : AKLT.Blueprint.Win.TailThresholdStatement
```

The proof chooses `M = max (geometryThreshold 64) (Nat.ceil (K ^ 2))`, where `K = tailConstant θ`. The ceiling ensures that `u ≥ M` implies `K² ≤ u`; consequently `K ≤ √u = shellSpacing u²`, and hence `K * shellSpacing u ^ (-2 : ℤ) ≤ 1`. The supplied tail estimate then gives the conclusion.

## Axioms

Output of `#print axioms main`:

```text
'AKLT.W.WIN073.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.WIN073.Main`
- Result: successful.
- Timing: 10.4 seconds wall time for the build invocation; Lean reported 5.1 seconds for this module.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/WIN073/Main.lean`, proving the requested theorem with the exact name and type.
- The threshold uses the geometric cutoff and the natural ceiling of the squared tail constant.
- Build succeeded with the requested Lake command.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No open issues or deviations.
