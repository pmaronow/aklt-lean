STATUS: PROVED

## Files

- `AKLT/W/GAP013/Main.lean`
- `/home/ubuntu/aklt/reports/LW/GAP013/report.md`

## Exported declaration

- `AKLT.W.GAP013.main : AKLT.Blueprint.Gap.NormalizedInteractionStatement`

## Axioms

`#print axioms AKLT.W.GAP013.main`:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.GAP013.Main`
- Result: successful; Lean reported the module built in 3.5 seconds.

## Open issues

None.

## ORCH-SUMMARY

- Delivered the exact requested theorem in `AKLT/W/GAP013/Main.lean`.
- The product reference has total mass one by finite product-sum factorization and the site probability hypotheses.
- Positivity of each product weight and `ψ`, together with `Z > 0`, proves positive probability; the expectation identity proves its total mass is one.
- Positive multiplication and division by `Z` give the pointwise lower and upper density bounds.
- Build succeeded; axioms are `[propext, Classical.choice, Quot.sound]`.
- No open issues or deviations.
