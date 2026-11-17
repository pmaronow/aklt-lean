STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC028/AKLT/W/REC028/Main.lean)

## Exported declaration

`AKLT.W.REC028.main : AKLT.Blueprint.Rec.LogEnclosureUpperStatement`

The proof bounds the logarithmic remainder by comparing derivatives on the compact interval `[0,t]`. It then rewrites the reciprocal logarithmic mean as `-log(s)/(1-s)`, uses `t=(1-s)/(1+s)`, and clears denominators only after proving positivity/nonzeroness. The final coercion identifies the real expression with the cast of the rational `logMeanUpper` definition.

## Axioms

`#print axioms AKLT.W.REC028.main`:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.REC028.Main`
- Result: successful.
- Timing: 16.686 seconds wall time for the final invocation; Lean reported 10 seconds for the module build.

## Open issues

None. The build emits tactic-style and deprecated-simp warnings; they do not affect the proof or its axiom set.

## ORCH-SUMMARY

- Delivered `AKLT/W/REC028/Main.lean` with the requested theorem and type.
- Proved by a derivative comparison for the finite logarithm remainder, followed by the rational-to-real enclosure conversion.
- `lake build AKLT.W.REC028.Main` succeeds.
- Exported theorem axioms: `propext`, `Classical.choice`, `Quot.sound`.
- No open mathematical issues or deviations.
