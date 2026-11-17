STATUS: PROVED

## Files

- `AKLT/W/GAP036/Main.lean`
- `/home/ubuntu/aklt/reports/LW/GAP036/report.md`

## Exported declaration

- `AKLT.W.GAP036.main : AKLT.Blueprint.Gap.BoxCoordinatesStatement`

The proof chooses the canonical `ZMod.val` centre lift, identifies the torus square with its lifted square, constructs the site equivalence using halo injectivity, and uses an involutive sitewise antipodal letter map according to lifted parity. Its boundary uses the lifted outer ring, including corners, so a changed halo site has a unique lifted coordinate where the boundary can differ.

## Axioms

`#print axioms AKLT.W.GAP036.main` reports:

```text
'AKLT.W.GAP036.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.GAP036.Main` — completed successfully; Lake reported the new module at 8.0 s and the full build at 15.9 s.
- Direct check: `lake env lean AKLT/W/GAP036/Main.lean` — completed successfully.

No existing project files were changed. No open proof obligations remain. Lean emitted only linter/deprecation warnings; they do not affect the successful build.

## ORCH-SUMMARY

- Delivered `AKLT/W/GAP036/Main.lean` with `AKLT.W.GAP036.main` at the exact requested type.
- The statement is proved from its hypotheses; no residual statements or helper axioms were introduced.
- The theorem's axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- Lake build succeeded; there are no open issues or decisions for the orchestrator.
