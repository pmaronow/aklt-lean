STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_Q059/AKLT/W/Q059/Main.lean)

## Exported declaration

- `AKLT.W.Q059.main : AKLT.Blueprint.Q.DensityVarianceStatement`

## Proof summary

The private helper `weighted_error_decomposition` proves

```lean
∑ x, p x * Complex.normSq (f x - c) =
  variance p f + Complex.normSq (complexMean p f - c)
```

for a normalized finite weight. It expands the squared complex norm around
the mean and cancels the cross term using normalization. For `main`, choose
`c = complexMean p f`. The helper gives that the `q` variance is at most the
`q` weighted squared error at this centre; the pointwise bound `q ≤ M * p`
compares that error with `M` times the corresponding `p` error, which equals
`M * variance p f`. The normalization components of the two positive
probability hypotheses suffice; strict positivity and `M ≥ 0` are not needed
for this particular implication.

## Axioms

`#print axioms AKLT.W.Q059.main`:

```text
'AKLT.W.Q059.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.Q059.Main` — succeeded; final incremental module build took 4.7 s.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.Q059.main` at the exact requested type in `AKLT/W/Q059/Main.lean`.
- The weighted squared-error decomposition is proved locally from finite-sum and complex norm identities.
- The requested Lake build succeeded.
- Axioms are `[propext, Classical.choice, Quot.sound]`.
- No residual statements or open issues.
