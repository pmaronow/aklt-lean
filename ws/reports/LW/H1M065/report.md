STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1M065/AKLT/W/H1M065/Main.lean)

## Exported declaration

- `AKLT.W.H1M065.main : AKLT.Blueprint.H1.AffineEvaluationStatementV2`

The proof expands evaluation into the finite sum of monomials. For a fixed token, the coordinate exponents are natural numbers with sum at most one, so that token's factor is constant or a single coordinate. It is therefore affine under the stated vector interpolation. The other token factors are unchanged, and finite sums preserve the identity. This proves the `c:reduce` leaf for arbitrary real coefficients.

## Axioms

`#print axioms AKLT.W.H1M065.main`:

```text
'AKLT.W.H1M065.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `PATH=$HOME/.elan/bin:$PATH lake build AKLT.W.H1M065.Main` — passed; Lake reported module build time 5.7 s (13.1 s command wall time).

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/H1M065/Main.lean` with the requested theorem and exact type.
- Status: proved; target module builds successfully.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No residual claims, deviations, or open issues.
