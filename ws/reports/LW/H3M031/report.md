STATUS: PROVED

## Files

- `AKLT/W/H3M031/Main.lean`

## Exported declaration

`AKLT.W.H3M031.main : AKLT.Blueprint.H3.StationaryCoefficientOffCentreStatementV2`

The proof unfolds the two coefficient definitions and simplifies using the explicit hypothesis `x + d.step ≠ kernelCentre`. This eliminates the extra V2 guard; the remaining guards and known-site cases reduce identically.

## Axioms

`#print axioms AKLT.W.H3M031.main`:

```text
'AKLT.W.H3M031.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.H3M031.Main` — succeeded; module reported 3.8s (command wall time 10.0s).
- Axiom check with `lake env lean /tmp/H3M031Axioms.lean` — succeeded; command wall time 5.7s.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/H3M031/Main.lean` with the requested theorem name and type.
- The theorem compiles from the frozen definitions using the non-centre destination premise.
- Axioms are `[propext, Classical.choice, Quot.sound]`.
- Build: `lake build AKLT.W.H3M031.Main` succeeded.
- No residual statements, deviations, or open issues.
