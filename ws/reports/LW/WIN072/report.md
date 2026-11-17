STATUS: PROVED

## Files

- `AKLT/W/WIN072/Main.lean`
- `/home/ubuntu/aklt/reports/LW/WIN072/report.md`

## Exported declaration

`AKLT.W.WIN072.main : AKLT.Blueprint.Win.TailExponentialStatement`

The proof sets `s = shellSpacing u` and `c = -Real.log θ`, converts the real power to an exponential, and bounds the exponential using `Real.pow_div_factorial_le_exp` at degree 10. The identities `s⁴ = u` and `(2u+1)² ≤ 9u²` give the required inverse-square decay.

## Axioms

`#print axioms AKLT.W.WIN072.main`:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

- `lake env lean AKLT/W/WIN072/Main.lean` — succeeded.
- `lake build AKLT.W.WIN072.Main` — succeeded; module build reported 7.4 s, total command elapsed 12.293 s.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.WIN072.main` with the exact requested type in `AKLT/W/WIN072/Main.lean`.
- The required Lake module build succeeded.
- Axiom output is `[propext, Classical.choice, Quot.sound]`.
- No residual statements or open issues.
