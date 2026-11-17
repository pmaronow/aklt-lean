STATUS: PARTIAL

## Files

- `AKLT/W/REC016/Main.lean`

## Exported declarations

- `AKLT.W.REC016.Residual_twoMeanIntervals : Prop` states just the needed
  lower bounds `22/25 ≤ I₂ᵗ` and `1 ≤ I₂⁰` for the two-neighbor case.
- `AKLT.W.REC016.Residual_logMeanPositive : Prop` states positivity of the
  logarithmic mean for positive arguments.
- `AKLT.W.REC016.Residual_logMeanMonotone : Prop` is the existing closed
  `AKLT.Blueprint.Rec.LogMeanMonotoneStatement`.
- `AKLT.W.REC016.Residual_crudeLogEnclosure : Prop` states the crude reciprocal
  logarithmic mean bound at `22/25`.
- `AKLT.W.REC016.main_of_residuals`
  proves `Residual_twoMeanIntervals → Residual_logMeanPositive →
  Residual_logMeanMonotone → Residual_crudeLogEnclosure →
  AKLT.Blueprint.Rec.BetaPrimeUniformStatement`.

The conditional proof uses `I₂ᵗ ≥ 22/25` and `I₂⁰ ≥ 1`, then compares the
logarithmic means and reciprocals. It applies the crude enclosure at `22/25`
and closes the remaining rational inequality by kernel normalization.

The requested unconditional declaration
`AKLT.W.REC016.main : AKLT.Blueprint.Rec.BetaPrimeUniformStatement` is not
present. The principal open obligation is `Residual_twoMeanIntervals`: derive
the two-neighbor removed-pair moment bounds for every departure by reindexing
the active spins, conditioning on outside-spin fibres, and applying the
degree-four and three-factor mean estimates. The three log-mean residuals also
remain open in this file; they correspond to positivity, monotonicity, and the
crude logarithm enclosure argument.

## Axioms

`#print axioms AKLT.W.REC016.main_of_residuals`:

```text
'AKLT.W.REC016.main_of_residuals' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

## Build

- `export PATH="$HOME/.elan/bin:$PATH"; lake build AKLT.W.REC016.Main`
- Successful final build; Lake reported the module compile in 4.6 seconds
  (about 9 seconds wall time for the command, with dependencies prebuilt).

## Open issues

- Prove `AKLT.W.REC016.Residual_twoMeanIntervals` from the finite-network
  definitions and proved libraries.
- Prove `AKLT.W.REC016.Residual_logMeanPositive`.
- Prove `AKLT.W.REC016.Residual_logMeanMonotone`.
- Prove `AKLT.W.REC016.Residual_crudeLogEnclosure`.
- Then export the requested unconditional theorem as
  `AKLT.W.REC016.main`.

## ORCH-SUMMARY

- Delivered a compiled conditional coefficient reduction in
  `AKLT/W/REC016/Main.lean`.
- Open residuals: `Residual_twoMeanIntervals`, `Residual_logMeanPositive`,
  `Residual_logMeanMonotone`, `Residual_crudeLogEnclosure`.
- The finite-network conditioning/moment argument is the main blocker.
- The exact requested theorem `AKLT.W.REC016.main` remains unproved.
- No existing files or statement definitions were edited.
