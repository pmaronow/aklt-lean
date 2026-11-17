STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_Q017/AKLT/W/Q017/Main.lean) — proves the requested leaf. No helper files were needed.

## Exported declaration

`AKLT.W.Q017.main : AKLT.Blueprint.Q.StarWitnessStatement`

The proof uses the coordinate basis vector supported at the all-zero configuration. Its coordinate there is `1`, so it is nonzero. A sparse matrix-column calculation gives each central-to-leaf Casimir eigenvalue `20` on this vector. The vector therefore lies in each projector's range and is fixed by each of the four projections. Their sum acts by `4`, proving the stated eigenvalue.

## Axioms

`#print axioms AKLT.W.Q017.main`:

```text
'AKLT.W.Q017.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build and verification

- `lake build AKLT.W.Q017.Main` — succeeded; 13.39 s wall time (Lake reports 7.4 s for the module).
- `lake env lean /tmp/Q017Axioms.lean` — succeeded; printed the axiom list above (14.17 s wall time). The temporary file only imports `AKLT.W.Q017.Main` and prints its axioms.

The build reports linter warnings for unused simp arguments, deprecated `if_pos`/`if_neg`, and one unnecessary `simpa`; there are no proof errors.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/Q017/Main.lean` with `AKLT.W.Q017.main` at the exact requested type.
- Status: PROVED; no residual declarations or extra premises.
- `lake build AKLT.W.Q017.Main` succeeds in 13.39 s wall time.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- Proof checks the sparse action on the all-zero basis vector and establishes it is nonzero.
- No existing files were changed; only the assigned new module and report were written.
- Non-blocking Lean linter warnings remain as listed above.
- No orchestrator decision or follow-up is required.
