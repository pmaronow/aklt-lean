STATUS: PARTIAL

## Files

- `AKLT/W/H1M047/Main.lean`
- `/home/ubuntu/aklt/reports/LW/H1M047/report.md`

## Delivered declarations

- `AKLT.W.H1M047.tensorPower_conjTranspose` proves that the conjugate transpose of `tensorPowerMatrix J g` is `tensorPowerMatrix J g.conjTranspose`.
- `AKLT.W.H1M047.tensorPower_left_unitary` and `AKLT.W.H1M047.tensorPower_right_unitary` prove tensor-power unitarity from `g.conjTranspose * g = 1`.
- `AKLT.W.H1M047.Residual_pauliRotationExpansion` states the tensor conjugation expansion into slotwise rotated Pauli coefficients.
- `AKLT.W.H1M047.Residual_pauliRotationCoefficients` states that orthogonal covariance fixes each Pauli coefficient after the transpose rotation.
- `AKLT.W.H1M047.main_of_residuals` combines these two residuals and tensor unitarity to prove `AKLT.Blueprint.H1.PauliRotationTransferStatement`.

The requested closed declaration `AKLT.W.H1M047.main : AKLT.Blueprint.H1.PauliRotationTransferStatement` is not delivered. The two open steps are proving the finite tensor expansion and proving the coefficient identity from `OrthogonalInvariant` by polynomial coefficient comparison.

## Axioms

`#print axioms` output for each exported theorem:

```text
 tensorPower_conjTranspose: [propext, Classical.choice, Quot.sound]
 tensorPower_left_unitary: [propext, Classical.choice, Quot.sound]
 tensorPower_right_unitary: [propext, Classical.choice, Quot.sound]
 main_of_residuals: [propext, Classical.choice, Quot.sound]
```

These are the permitted axioms. No `sorry`, `admit`, or added axiom is used.

## Build

Command: `lake build AKLT.W.H1M047.Main`

Result: successful, module compilation 8.3 seconds (Lake command wall time 16.9 seconds).

## Open issues

- Prove `AKLT.W.H1M047.Residual_pauliRotationExpansion` by expanding the tensor conjugation into single-site Pauli coordinates.
- Prove `AKLT.W.H1M047.Residual_pauliRotationCoefficients` by using covariance under the transpose rotation and comparing polynomial coefficients.
- Until both are proved, the exact closed `main` theorem is outstanding.

## ORCH-SUMMARY

- Added `AKLT/W/H1M047/Main.lean` with tensor-power adjoint and unitarity lemmas.
- Added two explicit residual propositions for the tensor expansion and coefficient covariance steps.
- `AKLT.W.H1M047.main_of_residuals` proves the target from those residual statements.
- Open: prove `AKLT.W.H1M047.Residual_pauliRotationExpansion` and `AKLT.W.H1M047.Residual_pauliRotationCoefficients`.
- The requested exact theorem `AKLT.W.H1M047.main` is not present; status is PARTIAL.
- Build passes; exported theorem axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
