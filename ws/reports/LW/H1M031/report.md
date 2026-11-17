STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_H1M031/AKLT/W/H1M031/Main.lean`

## Exported declaration

- `AKLT.W.H1M031.main : AKLT.Blueprint.H1.DifferenceStructureStatement`

The proof shows that scalar multiplication by `MvPolynomial.C c` preserves the support exponents of `q`, then applies `support_sub` to place the difference support inside `p.support ∪ q.support`. The affine and supported-vector properties follow pointwise from that inclusion. For orthogonal invariance, polynomial evaluation is expanded through subtraction, multiplication, and the constant, then the two input covariance equalities are applied.

## Axiom audit

`#print axioms AKLT.W.H1M031.main`:

```text
'AKLT.W.H1M031.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.H1M031.Main`
- Result: success; target module built in 3.3 seconds (build completed in about 9 seconds wall time).

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.H1M031.main` with the exact requested type.
- The requested Lake target builds successfully.
- Axiom dependencies are only `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements or deviations.
- No open issues or decisions for the orchestrator.
