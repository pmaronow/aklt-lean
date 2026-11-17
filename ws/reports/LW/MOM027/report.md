STATUS: PROVED

## Files

- `AKLT/W/MOM027/Main.lean`
- `/home/ubuntu/aklt/reports/LW/MOM027/report.md`

## Exported declaration

- `AKLT.W.MOM027.main : AKLT.Blueprint.Mom.MeanPathEndpointsStatement`

The proof unfolds the finite U-site mean and computes the endpoint product integrals from the explicit icosahedral atom list. At zero, the mean is `(3/5)e₁`; at `2π/3`, the denominator is `1/2` and each numerator coordinate is zero. It then evaluates the squared norms. The U-law-to-moment identity is proved locally from the definitions; no other blueprint leaf is used.

## Axioms

`#print axioms AKLT.W.MOM027.main`:

```text
'AKLT.W.MOM027.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.MOM027.Main`
- Result: success
- Timing: target built in 6.2 s; command wall time 11.530 s

## Open issues

None.

## ORCH-SUMMARY

- Delivered the exact requested theorem in `AKLT/W/MOM027/Main.lean`.
- Status: PROVED; the requested Lake module build succeeds.
- Exported declaration: `AKLT.W.MOM027.main : AKLT.Blueprint.Mom.MeanPathEndpointsStatement`.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- No residual statements, deviations, or open issues.
