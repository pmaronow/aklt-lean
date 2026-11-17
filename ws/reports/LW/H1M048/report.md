STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1M048/AKLT/W/H1M048/Main.lean)

## Exported declaration

`AKLT.W.H1M048.main : AKLT.Blueprint.H1.CayleyTensorCommutationStatement`

The proof normalizes `I - it σⱼ` by `sqrt (1 + t²)`. Direct Pauli matrix calculations establish that the normalized matrix is unitary and has determinant one. The denominator is nonzero because `1 + t² > 0`. A tensor power of a scalar multiple is the scalar raised to `J.card` times the tensor power; that scalar is nonzero, so it cancels from the commutation equality.

## Axioms

`#print axioms AKLT.W.H1M048.main`:

```text
'AKLT.W.H1M048.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake env lean AKLT/W/H1M048/Main.lean` — succeeded.
- `lake build AKLT.W.H1M048.Main` — succeeded; module compile 9.3 s, command wall time 17.34 s (`real`, `/usr/bin/time -p`).
- Final build emitted no warnings.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.H1M048.main` with the exact requested type.
- Proof and build complete; `lake build AKLT.W.H1M048.Main` succeeds.
- Axioms: `[propext, Classical.choice, Quot.sound]`.
- No deviations or open declarations.
