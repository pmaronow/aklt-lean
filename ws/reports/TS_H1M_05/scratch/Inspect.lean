import AKLT.Blueprint.H1.NodesSector

/- Inspection only: no theorems, proofs, axioms, or sorry declarations. -/
set_option pp.universes true
set_option pp.proofs false

#print AKLT.Blueprint.H1.SectorWeightBasisStatement
#print AKLT.Blueprint.H1.SpanWeightLatticeStatement
#print AKLT.Blueprint.H1.SpinAdjointStatement
#print AKLT.Blueprint.H1.SpinCommutatorStatement
#print AKLT.Blueprint.H1.WeightLadderTransferStatement
#print AKLT.Blueprint.H1.CommonWeightEigenvectorStatement
#print AKLT.Blueprint.H1.LadderWalkStatement
#print AKLT.Blueprint.H1.PositiveSpectrumStatement
#print AKLT.Blueprint.H1.WeightLadder
#print AKLT.Blueprint.H1.SpinStable
#print AKLT.Defs.PositiveOn
#print AKLT.Defs.eigenvaluesOn

#check @AKLT.Blueprint.H1.SectorWeightBasisStatement
#check @AKLT.Blueprint.H1.SpanWeightLatticeStatement
#check @AKLT.Blueprint.H1.CommonWeightEigenvectorStatement
#check @AKLT.Blueprint.H1.PositiveSpectrumStatement
#check Module.End.eigenspaces_iSupIndep
#check LinearMap.IsSymmetric.apply_eigenvectorBasis
#check LinearMap.IsSymmetric.hasEigenvalue_eigenvalues
#check LinearMap.IsSymmetric.conj_eigenvalue_eq_self
#check Matrix.toEuclideanLin_conjTranspose_eq_adjoint

open AKLT.Defs AKLT.Blueprint.H1
variable (J : Finset (Fin 20)) (S : Submodule ℂ (TensorSpace J))
variable (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
#synth Fintype (J → Fin 2)
#synth FiniteDimensional ℂ (TensorSpace J)
#synth InnerProductSpace ℂ S
#synth FiniteDimensional ℂ S
#synth CompleteSpace S
#synth Fintype (ExchangeBasis π r ε)
