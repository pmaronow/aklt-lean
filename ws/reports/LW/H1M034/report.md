STATUS: PROVED

## Files

- `AKLT/W/H1M034/Main.lean`
- `/home/ubuntu/aklt/reports/LW/H1M034/report.md`

## Exported declaration

`AKLT.W.H1M034.main : AKLT.Blueprint.H1.SpanWeightLatticeStatement`

The proof places the given span inside the supremum of eigenspaces indexed by the weights appearing in the finite family. Mathlib's `Module.End.eigenspaces_iSupIndep` shows that an eigenspace indexed by a new weight is disjoint from this supremum. Hence a nonzero eigenvector must have a weight occurring in the family, and the corresponding lattice premise supplies its integer offset. Repeated weights and zero family members require no special cases.

## Axioms

`#print axioms AKLT.W.H1M034.main`:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.H1M034.Main`
- Result: success
- Timing: 8.9 s total; Lean reported 3.7 s for the module.

## Open issues

None.

## ORCH-SUMMARY

- Delivered the exact requested theorem in `AKLT/W/H1M034/Main.lean`.
- The theorem compiles and has only the permitted classical/propositional axioms listed above.
- The span argument uses independence of distinct eigenspaces; it makes no independence or normalization assumption on the original family.
- No residual statements or deviations remain.
