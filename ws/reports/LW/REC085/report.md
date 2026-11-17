STATUS: PROVED

## Files

- `AKLT/W/REC085/Main.lean`
- `/home/ubuntu/aklt/reports/LW/REC085/report.md`

## Exported declaration

- `AKLT.W.REC085.main : AKLT.Blueprint.Rec.RenewalFiniteIterationStatement`

## Proof outline

The weighted `RenewalRows` premise supplies a summable majorant for every application of `renewalOp` to a bounded nonnegative function. The proof establishes explicit summability, positivity, monotonicity, additivity, and boundedness preservation for that operator. It extends the recurrence to nonpositive integer depths using `F ≤ 2`, then proves the requested result by induction on the finite iterate and reindexes the finite source sum.

## Axioms

`#print axioms AKLT.W.REC085.main`:

```text
'AKLT.W.REC085.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the permitted axioms. No residual propositions or additional helper files remain.

## Build

- Command: `lake build AKLT.W.REC085.Main`
- Result: success
- Lean module build time reported by Lake: 6.2 s (13.1 s wall time for the build command)

## Open issues

None.

## ORCH-SUMMARY

Delivered `AKLT.W.REC085.main` with the exact requested statement in `AKLT/W/REC085/Main.lean`.
The finite iteration proof compiles with explicit summability premises for operator applications.
Axiom output is `[propext, Classical.choice, Quot.sound]`.
`lake build AKLT.W.REC085.Main` succeeded.
No residual statements, deviations, or open issues.
