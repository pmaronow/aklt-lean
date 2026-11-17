module
public import AKLT.Blueprint.Q.NodesSplits
public import AKLT.Uniq.Polynomial

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section

open AKLT.Challenge

namespace AKLT.W.Q035

theorem statePolynomial_eq_encode {L N : Size} (ψ : Hilbert L N) :
    AKLT.Blueprint.Q.statePolynomial ψ = AKLT.Uniq.encode ψ := by
  classical
  unfold AKLT.Blueprint.Q.statePolynomial AKLT.Uniq.encode AKLT.Uniq.basisScale
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [MvPolynomial.C_mul_monomial]
  congr 1
  ring

theorem main : AKLT.Blueprint.Q.StateCentreDegreeStatement := by
  intro L N ψ x m hm
  have hhom := AKLT.Uniq.encode_physical (L := L) (N := N) ψ x
  have hweight := hhom (MvPolynomial.mem_support_iff.mp
    (by simpa [statePolynomial_eq_encode] using hm))
  rw [AKLT.Uniq.siteWeight_degree] at hweight
  exact hweight

end AKLT.W.Q035

#print axioms AKLT.W.Q035.main
