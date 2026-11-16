import AKLT.W.H1M047.Polynomial
import AKLT.W.H1M047.Tensor

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.H1

namespace AKLT.W.H1M047

/-- Orthogonal covariance of a vector-affine polynomial transfers to
commutation of its Pauli operator with the supplied unitary tensor power. -/
theorem main : AKLT.Blueprint.H1.PauliRotationTransferStatement := by
  intro J p ha hs hi g hg R hR hc
  have hfixed : rotatedPauliOperator J p R = pauliOperator J p := by
    ext σ τ
    simp only [rotatedPauliOperator, pauliOperator]
    apply Finset.sum_congr rfl
    intro b _
    rw [rotation_coefficients J p ha hs hi R hR b]
  have hconj : tensorPowerMatrix J g * pauliOperator J p *
      (tensorPowerMatrix J g).conjTranspose = pauliOperator J p := by
    rw [pauli_rotation_expansion J p g hg R hc, hfixed]
  change pauliOperator J p * tensorPowerMatrix J g =
    tensorPowerMatrix J g * pauliOperator J p
  calc
    pauliOperator J p * tensorPowerMatrix J g =
        (tensorPowerMatrix J g * pauliOperator J p *
          (tensorPowerMatrix J g).conjTranspose) * tensorPowerMatrix J g := by rw [hconj]
    _ = tensorPowerMatrix J g * pauliOperator J p *
        ((tensorPowerMatrix J g).conjTranspose * tensorPowerMatrix J g) := by
      simp only [mul_assoc]
    _ = tensorPowerMatrix J g * pauliOperator J p := by
      rw [tensorPower_left_unitary J g hg, mul_one]

end AKLT.W.H1M047
