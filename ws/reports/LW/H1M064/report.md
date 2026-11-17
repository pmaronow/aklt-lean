STATUS: PROVED

## Files

- `AKLT/W/H1M064/Main.lean`
- `/home/ubuntu/aklt/reports/LW/H1M064/report.md`

## Exported declaration

- `AKLT.W.H1M064.main : AKLT.Blueprint.H1.DifferenceEvaluationStatementV2`

The proof unfolds the real difference and evaluation definitions. `simp` applies
the `MvPolynomial` evaluation/map compatibility rule and evaluation of
subtraction, multiplication, and constants. The threshold `c` stays in `ℝ`.

Paper label: `c:reduce`.

## Axioms

Output of `#print axioms AKLT.W.H1M064.main`:

```text
'AKLT.W.H1M064.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

Command: `lake build AKLT.W.H1M064.Main`

Result: success; wall time 8.37 s, reported module build time 3.5 s.

## Open issues

None.

## ORCH-SUMMARY

- Delivered the exact requested theorem in `AKLT/W/H1M064/Main.lean`.
- Proof compiled with the mandated Lake build command.
- Axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
- The real threshold is used directly; no rational conversion is made.
- No open issues or deviations.
