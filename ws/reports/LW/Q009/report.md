STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_Q009/AKLT/W/Q009/Main.lean)

## Exported declaration

`AKLT.W.Q009.main : AKLT.Blueprint.Q.QuarticKernelDegreeStatement`

The proof bounds each linear factor by degree one, applies the total-degree power and product inequalities, then uses the branch-specific exponent identity. The `j ≤ k` and `k < j` branches simplify the natural-number subtractions before closing the exponent sum.

## Axioms

`#print axioms AKLT.W.Q009.main`:

```text
'AKLT.W.Q009.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

Command: `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.Q009.Main`

Result: succeeded; 16.17 seconds elapsed (module compile reported 7.3 seconds). Lean emitted two deprecation warnings for the `if_pos` and `if_neg` simp lemmas; they do not affect the proof.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/Q009/Main.lean` with the requested theorem and type.
- Proved both kernel branches using polynomial total-degree bounds and omega arithmetic.
- `lake build AKLT.W.Q009.Main` succeeded.
- Axioms are `[propext, Classical.choice, Quot.sound]`.
- No residual statements, deviations, or open issues.
