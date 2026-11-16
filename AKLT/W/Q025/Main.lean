import AKLT.Blueprint.Q.NodesPolynomial
import AKLT.Uniq.Edge

noncomputable section

open scoped BigOperators
open AKLT.Defs AKLT.Challenge

namespace AKLT.W.Q025

/-- The state polynomial is exactly the normalized polynomial encoding used
by the proved edge kernel theorem. -/
theorem statePolynomial_eq_encode {L N : Size} (ψ : Hilbert L N) :
    AKLT.Blueprint.Q.statePolynomial ψ = AKLT.Uniq.encode ψ := by
  classical
  unfold AKLT.Blueprint.Q.statePolynomial AKLT.Uniq.encode AKLT.Uniq.basisScale
  apply Finset.sum_congr rfl
  intro σ _
  rw [MvPolynomial.C_mul_monomial]
  congr 1
  ring

theorem main : AKLT.Blueprint.Q.SpectatorDivisibilityStatement := by
  intro _ L N e ψ hP
  have hdiv : AKLT.Challenge.singlet e ∣ AKLT.Uniq.encode ψ :=
    (AKLT.Uniq.edgeKernel L N e ψ).mp hP
  simpa [statePolynomial_eq_encode] using hdiv

#print axioms main

end AKLT.W.Q025
