STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_H3C037/AKLT/W/H3C037/Main.lean`
- `/home/ubuntu/aklt/reports/LW/H3C037/report.md`

## Exported declaration

`AKLT.W.H3C037.main : CertData.H3.Bridge.NumericScaleLeaf`

The proof unfolds `resultValue`, `finalNumerator`, and `finalDenominator`, casts the natural-number expressions to `ℚ`, obtains nonzeroness of the denominator from `0 < E.denominator`, then clears denominators with `field_simp`.

## Axioms

`#print axioms AKLT.W.H3C037.main`:

```text
[propext, Classical.choice, Quot.sound]
```

These are allowed axioms under the brief.

## Build

Command: `lake build AKLT.W.H3C037.Main`

Result: successful; Lean reported `Built AKLT.W.H3C037.Main (9.8s)` and `Build completed successfully (8973 jobs)`.

## Open issues and deviations

- None for the proof.
- The requested first attempt with a different cheaper model could not be performed: no model-switch tool was available, and the brief forbids sub-agents.

## ORCH-SUMMARY

- Delivered `AKLT.W.H3C037.main` proving the exact `NumericScaleLeaf` statement.
- Build succeeded with `lake build AKLT.W.H3C037.Main`.
- Axioms: `[propext, Classical.choice, Quot.sound]`.
- No remaining proof issues.
- Deviation: first attempt was not made with a cheaper model because model switching was unavailable and sub-agents were forbidden.
