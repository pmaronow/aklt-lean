STATUS: PROVED

## Files

- `AKLT/W/MOM005/Main.lean`
- `/home/ubuntu/aklt/reports/LW/MOM005/report.md`

## Exported declaration

`AKLT.W.MOM005.main : AKLT.Blueprint.Mom.FourthScalarMomentStatement`, where
`FourthScalarMomentStatement` unfolds to
`∀ i, moment (fun v => v i ^ 4) = 1 / 5`.

## Proof

The proof reduces the finite product sum over `Fin 3 × Fin 2 × Fin 2` to its three coordinate cases and the two sign sums. It establishes the golden ratio square identity and `icoRadius ^ 4 = 5 * goldenRatio ^ 2`, then uses `1 + goldenRatio ^ 4 = 3 * goldenRatio ^ 2`. After clearing the positive radius denominator, `nlinarith` closes each scalar case. This follows the finite-sum calculation in paper label `l:moments`, lines 66–72.

## Axioms

`#print axioms AKLT.W.MOM005.main`:

```text
'AKLT.W.MOM005.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

Command: `lake build AKLT.W.MOM005.Main`

Result: successful; Lake reported the target build at 9.4 seconds (19.3 seconds total command wall time).

## Open issues

None.

## ORCH-SUMMARY

- Delivered and compiled `AKLT.W.MOM005.main` with the requested type.
- Reported axioms are `[propext, Classical.choice, Quot.sound]`.
- Proof evaluates all three coordinates and both independent signs, then uses the stated golden ratio and radius algebra.
- No residual statements, deviations, or open issues.
