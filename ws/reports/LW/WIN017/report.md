STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_WIN017/AKLT/W/WIN017/Main.lean)
- [report.md](/home/ubuntu/aklt/reports/LW/WIN017/report.md)

All proof helpers in `Main.lean` are private. The only exported declaration is:

```lean
theorem AKLT.W.WIN017.main :
  AKLT.Blueprint.Win.PlaquetteReconstructionStatement
```

## Axiom audit

`#print axioms AKLT.W.WIN017.main`:

```text
'AKLT.W.WIN017.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.WIN017.Main` — succeeded; wall time 23.2s (Lean module build reported 12s).
- `lake env lean /tmp/WIN017Axioms.lean` — succeeded; wall time 7.1s; confirmed the exact theorem name/type and axiom output.

## Proof outline and open issues

Horizontal plaquette coefficients reduce to adjacent tail differences. The four local edge coefficients at each vertex are identified from `ChainEven` after using `ChainNN` to restrict incidence to the four nearest-neighbour edges. Summing that local relation on the finite interval above a vertical edge telescopes; `ChainInBox` removes the top endpoint and the supplied column flux handles the lower tail. The condition on `P` then lets each finite plaquette sum recover both edge coefficients. Non-nearest-neighbour coefficients vanish on both sides.

Open issues: none.

## ORCH-SUMMARY

- Delivered `AKLT.W.WIN017.main` with the exact required type.
- The theorem compiles with `lake build AKLT.W.WIN017.Main`.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound` only.
- Helper declarations are private; no other declarations are exported.
- No residual statements, limitations, or deviations remain.
- Orchestrator action: accept the proved leaf and report.
