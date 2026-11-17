STATUS: PROVED

## Files

- `AKLT/W/H1M045/Main.lean`

## Exported declaration

`AKLT.W.H1M045.main : AKLT.Blueprint.H1.AdjointPauliCoordinatesStatement`

The proof assigns real coordinates from the entries of each conjugated Pauli matrix. It proves each conjugate is Hermitian and traceless, then expands it in the three Pauli matrices. The determinant hypothesis is unused; unitarity suffices for tracelessness, while Hermiticity follows from conjugation by any matrix.

## Axioms

`#print axioms AKLT.W.H1M045.main`:

```text
'AKLT.W.H1M045.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.H1M045.Main` — succeeded; Lake reported the module built in 8.8s.
- `lake env lean /tmp/H1M045Axioms.lean` — succeeded; used to capture the axiom output above.

## Open issues

None.

## ORCH-SUMMARY

- Delivered the requested theorem in `AKLT/W/H1M045/Main.lean`.
- The requested module build succeeded.
- Exported theorem axioms are `[propext, Classical.choice, Quot.sound]`.
- The determinant premise is stronger than required and is unused.
- No open proof obligations or deviations remain.
