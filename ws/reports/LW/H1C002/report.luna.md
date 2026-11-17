STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1C002/AKLT/W/H1C002/Main.lean)
- This report: `/home/ubuntu/aklt/reports/LW/H1C002/report.md`

## Delivered declarations

- `AKLT.W.H1C002.ResidualCurrentReconstruction : Prop` states the exact current-sector floor reconstruction from `ClearsDenominator`.
- `AKLT.W.H1C002.ResidualNextReconstruction : Prop` states the corresponding exact next-sector floor reconstruction.
- `AKLT.W.H1C002.ResidualComplexReconstruction : Prop` states complex-to-rational sector-entry reconstruction for the inverted threshold difference; this includes imaginary cancellation.
- `AKLT.W.H1C002.ResidualRationalLinearity : Prop` states distribution of the rational sector form over the current-minus-threshold-times-next polynomial.
- `AKLT.W.H1C002.main_of_residuals` proves `AKLT.Cert.H1.Production.TopLeaves.thresholdScale` from those four explicit residual propositions. Its arithmetic gives the scale `15 * D₀ * q`.

The requested theorem `AKLT.W.H1C002.main : AKLT.Cert.H1.Production.TopLeaves.thresholdScale` is not delivered because the residual propositions remain unproved from the frozen hypotheses.

## Axioms

`#print axioms AKLT.W.H1C002.main_of_residuals`:

```text
'AKLT.W.H1C002.main_of_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the permitted axioms. No `sorry`, `admit`, or other forbidden construction is used.

## Build

- `lake build AKLT.W.H1C002.Main` — succeeded, 7.5 seconds (8963 jobs).
- `lake env lean AKLT/W/H1C002/Main.lean` — the final source compiled as part of the successful Lake build.

## Open issues

- Prove `ResidualCurrentReconstruction` and `ResidualNextReconstruction` by deriving integrality of the scaled rational sector sums from the coefficient condition, then eliminating `Int.floor` exactly.
- Prove `ResidualComplexReconstruction`: show the imaginary contributions cancel for the inverted difference and identify its real part with `rationalSectorEntry`.
- Prove `ResidualRationalLinearity` by distributing the polynomial difference and scalar through the Pauli and sector sums.
- Once those are proved, apply `main_of_residuals` to provide the requested exact theorem `AKLT.W.H1C002.main`.

## ORCH-SUMMARY

- Delivered a compiled conditional proof of `thresholdScale` in `AKLT/W/H1C002/Main.lean`.
- The exact requested theorem `AKLT.W.H1C002.main` remains open.
- Open residuals: `ResidualCurrentReconstruction`, `ResidualNextReconstruction`, `ResidualComplexReconstruction`, `ResidualRationalLinearity`.
- The residuals isolate the floor, imaginary-cancellation, and linearity obligations; all are closed `Prop` definitions.
- The factor calculation in `main_of_residuals` is proved and uses the exact scale `15 D₀ q`.
- Lake build succeeded; axiom output is permitted.
- No existing project files were edited.
