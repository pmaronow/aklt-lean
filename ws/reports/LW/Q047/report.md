STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_Q047/AKLT/W/Q047/Main.lean)
- [report.md](/home/ubuntu/aklt/reports/LW/Q047/report.md)

## Exported declaration

`AKLT.W.Q047.main : AKLT.Blueprint.Q.GroundQuotientVarianceStatement`

The proof expands `complexMean` and `variance` into their finite sums. The density identity cancels the ground evaluation in the mean, leaving `weightedInner (torusReference ...) (frameEval ... B) (frameEval ... ψ) / ‖B‖`. Orthogonality and the supplied inner-product identity make that zero. In the variance, the pointwise squared-modulus density cancels the squared quotient denominator; the remaining sum is `weightedNorm (torusReference ...) (frameEval ... ψ)`. The diagonal case of the supplied inner-product identity identifies it with `‖ψ‖²`.

## Axioms

`#print axioms AKLT.W.Q047.main`:

```text
'AKLT.W.Q047.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.Q047.Main`
- Result: success; Lake reported `Built AKLT.W.Q047.Main (6.2s)`.
- A separate `lake env lean /tmp/Q047Axioms.lean` invocation checked the declaration and printed its axioms.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/Q047/Main.lean` with the requested theorem name and type.
- The theorem builds from the frozen statement's hypotheses.
- Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements, deviations, or open issues.
- Build command: `lake build AKLT.W.Q047.Main` (success).
