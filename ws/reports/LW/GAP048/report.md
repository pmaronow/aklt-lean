STATUS: PROVED

Files:
- `AKLT/W/GAP048/Main.lean`
- `/home/ubuntu/aklt/reports/LW/GAP048/report.md`

Exported declaration:
- `AKLT.W.GAP048.main : AKLT.Blueprint.Gap.ShellAbsorptionStatement`

Proof route: positivity of the trace and nonnegative stochastic row weights give positive transition weights along the path. The unskipped successor after the successful trial then applies `SurgeryKernels.identical` to establish agreement on its far region. Inductively, each later exceptional row is a point mass at the current pair; each nonexceptional row extends agreement using shell containment and `fixed_exterior`. The target far sites lie in the established far region by the trial index bound.

`#print axioms AKLT.W.GAP048.main`:
```text
'AKLT.W.GAP048.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Build:
- `lake build AKLT.W.GAP048.Main` — passed; Lean module build reported 6.0 s (final build).

Open issues: none.

## ORCH-SUMMARY

- Delivered `AKLT.W.GAP048.main` with the requested exact type in `AKLT/W/GAP048/Main.lean`.
- `lake build AKLT.W.GAP048.Main` passes.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements, deviations, or open issues.
