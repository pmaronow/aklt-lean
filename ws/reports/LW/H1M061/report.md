STATUS: PROVED

## Files

- `AKLT/W/H1M061/Main.lean`
- `/home/ubuntu/aklt/reports/LW/H1M061/report.md`

## Exported declaration

- `AKLT.W.H1M061.main : AKLT.Blueprint.H1.RationalEmbeddingStructureStatementV2`

The proof transfers each condition along `MvPolynomial.support_map_subset`: every exponent in the mapped polynomial's support already belongs to the original support, so the original vector-degree and absent-token bounds apply unchanged.

## Axioms

`#print axioms AKLT.W.H1M061.main`:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.H1M061.Main`
- Result: successful; Lean reported the module built in 3.5s.

## Open issues

None.

## ORCH-SUMMARY

Delivered `AKLT.W.H1M061.main` at the exact requested name and type in `AKLT/W/H1M061/Main.lean`.
The proof uses support inclusion under `MvPolynomial.map` to preserve vector-affine and supported-vector bounds.
The requested Lake module build succeeded.
Axioms are `propext`, `Classical.choice`, and `Quot.sound`.
No open issues or deviations.
