STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_MOM028/AKLT/W/MOM028/Main.lean)
- [report.md](/home/ubuntu/aklt/reports/LW/MOM028/report.md)

## Exported declaration

`AKLT.W.MOM028.main : AKLT.Blueprint.Mom.MeanCovarianceStatement`

The proof expands the finite U-site functional to the twelve icosahedron atoms and establishes the scalar normalizer and vector numerator formulas directly. Orthogonality preserves dot products and unit lengths; the normalizer stays fixed, the numerator rotates covariantly, and scalar division commutes with `mulVec`.

## Axioms

Output of `#print axioms AKLT.W.MOM028.main`:

```text
'AKLT.W.MOM028.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.MOM028.Main` — succeeded; module build reported 10s (15.3s wall time for the command).

## Open issues

None.

## ORCH-SUMMARY

- Proved the exact frozen statement as `AKLT.W.MOM028.main`.
- Delivered `AKLT/W/MOM028/Main.lean`; no helper modules were needed.
- Directly verified the cubic scalar and quartic vector mean formulas from the explicit finite support.
- `lake build AKLT.W.MOM028.Main` succeeds.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound` only.
- No open issues or deviations; orchestrator action: none.
