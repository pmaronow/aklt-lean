import AKLT.Blueprint.Q.NodesPolynomial
import AKLT.Blueprint.Q.NodesSplits

-- Inspection only: this file contains no theorem declarations or proofs.
set_option pp.universes true

#print AKLT.Blueprint.Q.SpectatorDivisibilityStatement
#print AKLT.Blueprint.Q.SingletNonassociateStatement
#print AKLT.Blueprint.Q.IncidentKernelStatement
#print AKLT.Blueprint.Q.PairDiagonalRankStatement
#print AKLT.Blueprint.Q.PairTopInclusionStatement
#print AKLT.Blueprint.Q.PairTopDimensionStatement
#print AKLT.Blueprint.Q.FourVariableDeterminantPrimeStatement
#print AKLT.Blueprint.Q.DeterminantPrimeEmbeddingStatement

#check MvPolynomial.irreducible_mul_X_add
#check MvPolynomial.prime_rename_iff
#check MvPolynomial.isUnit_iff_eq_C_of_isReduced
#check Submodule.re_inner_starProjection_eq_normSq
#check Module.End.eigenspace_def
