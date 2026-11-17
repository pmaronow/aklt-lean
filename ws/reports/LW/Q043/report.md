STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_Q043/AKLT/W/Q043/Main.lean`
- `/home/ubuntu/aklt/reports/LW/Q043/report.md`

## Exported declaration

`AKLT.W.Q043.main : AKLT.Blueprint.Q.GroundTransformStatement`

The proof unfolds `groundTransform` and `groundQuotient`. For the weighted norm identity, it applies the assumed pointwise density law inside the finite sum and uses `Complex.normSq_mul`, `Complex.normSq_div`, and `Complex.normSq_ofReal`. The quotient and pointwise inverse identities follow by cancellation, using `B L N ≠ 0` for the norm denominator and the assumed nonzero ground evaluations for the evaluation denominator.

## Axioms

Output of `#print axioms AKLT.W.Q043.main`:

```text
'AKLT.W.Q043.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

Command: `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.Q043.Main`

Result: successful; Lean reported module build in 5.7 s, command wall time 12.5 s.

The axiom check was run with `lake env lean /tmp/Q043Axioms.lean` and produced the output above.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.Q043.main` with the exact requested type in `AKLT/W/Q043/Main.lean`.
- Status: PROVED; `lake build AKLT.W.Q043.Main` succeeded.
- The theorem uses only the stated hypotheses and has axioms `[propext, Classical.choice, Quot.sound]`.
- No deviations or open issues.
