STATUS: PROVED

## Files

- `AKLT/W/Q004/Main.lean`

## Exported declaration

- `AKLT.W.Q004.main : AKLT.Blueprint.Q.RotationDisplacementStatement`

## Proof summary

Omega reduces the explicit exponent range to `k = 1` or `k = 2`. For each case, the squared displacement simplifies to a rational multiple of the planar squared norm: `404 / 10201` for `k = 1`, and `1600 / 10201` for `k = 2`. The unit norm bounds the planar squared norm by one; rational arithmetic closes both estimates.

## Axioms

`#print axioms AKLT.W.Q004.main`:

```text
'AKLT.W.Q004.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.Q004.Main` — succeeded; 16.6 s wall time (Lake reported 8.6 s for the module).
- Axiom inspection: `lake env lean /tmp/Q004Axioms.lean` — succeeded.

## Open issues

None.

## ORCH-SUMMARY

- Delivered the exact requested theorem in `AKLT/W/Q004/Main.lean`.
- The requested Lake build succeeds.
- Axiom dependencies are `propext`, `Classical.choice`, and `Quot.sound`.
- No open issues or deviations.
