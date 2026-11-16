import AKLT.Blueprint.Q.NodesPolynomial
import AKLT.Uniq.Polynomial

noncomputable section
open AKLT.Challenge

namespace AKLT.W.Q023

/-- The stated support condition is exactly the weighted-homogeneity
condition used by the polynomial coordinate library. -/
theorem siteHomogeneous_isPhysical {L N : Size} {p : SpinorPolynomial L N}
    (hp : AKLT.Blueprint.Q.siteHomogeneous p (fun _ => 4)) :
    AKLT.Uniq.IsPhysical p := by
  intro x d hd
  rw [AKLT.Uniq.siteWeight_degree]
  exact hp d (MvPolynomial.mem_support_iff.mpr hd) x

theorem encoded_polynomial_eq {L N : Size} (p : SpinorPolynomial L N) :
    AKLT.Blueprint.Q.statePolynomial (AKLT.Defs.polynomialState p) =
      AKLT.Uniq.encode (AKLT.Uniq.decode p) := by
  classical
  simp [AKLT.Blueprint.Q.statePolynomial, AKLT.Defs.polynomialState,
    AKLT.Uniq.encode, AKLT.Uniq.decode, AKLT.Uniq.basisScale, mul_comm]
  apply Finset.sum_congr rfl
  intro σ hσ
  let C : ℂ →+* SpinorPolynomial L N := MvPolynomial.C
  have hscale :
      (∏ x : Site L N, C (Real.sqrt (Nat.choose 4 (σ x).val : ℝ) : ℂ)) =
        C (∏ x : Site L N, (Real.sqrt (Nat.choose 4 (σ x).val : ℝ) : ℂ)) := by
    simp [C]
  rw [hscale, ← map_mul C, mul_comm (MvPolynomial.monomial _ _),
    MvPolynomial.C_mul_monomial, mul_one]

theorem main : AKLT.Blueprint.Q.CoefficientReconstructionStatement := by
  intro L N p hp
  rw [encoded_polynomial_eq]
  exact AKLT.Uniq.encode_decode (siteHomogeneous_isPhysical hp)

end AKLT.W.Q023
