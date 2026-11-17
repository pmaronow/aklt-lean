module
public import AKLT.W.H1C020.Audit
public import AKLT.W.H1C020.ResidualRing
public import AKLT.W.H1C020.ResidualCenter

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-!
The production moment-polynomial leaf.  Integer moment numerators, exact
denominator clearing, transfer expansion, and original-token inversion are in
Local, Normalization, Transfer, Inversion, and GroupTokens.  The two spin
contraction steps are proved in ResidualRing (finite Fubini over the eight
ring sites) and ResidualCenter (integration of the passage spin).
-/
namespace AKLT.W.H1C020

open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

/-- Composition of the two spin-contraction identities with the algebra of
the packed constructor. -/
theorem main_of_residuals (hF : Residual_ringFubini) (hC : Residual_centerContraction) :
    AKLT.Cert.H1.Production.Leaves.momentPolynomial := by
  intro π hπ r I hI ss hg out hout next
  rw [networkNumerator_clear ss out next (network_localValidity π r I ss hg),
    rationalNetwork_of_residuals hF hC π hπ r I hI ss hg out hout next]
  cases next <;> rfl

theorem main : AKLT.Cert.H1.Production.Leaves.momentPolynomial :=
  main_of_residuals ringFubini_holds centerContraction_holds

end AKLT.W.H1C020
