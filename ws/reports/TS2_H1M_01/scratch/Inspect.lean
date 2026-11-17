import AKLT.Blueprint.H1.NodesV2Pauli
import Mathlib.Analysis.Matrix.Order

#print AKLT.Blueprint.H1.PauliExpansionStatementV2
#print AKLT.Blueprint.H1.PauliProductTraceStatementV2
#print AKLT.Blueprint.H1.InversionPolynomialStatementV2
#print AKLT.Blueprint.H1.ProductDensityPositiveStatementV2
#print AKLT.Blueprint.H1.InversionBallStatementV2
#print AKLT.Blueprint.H1.RationalEmbeddingStructureStatementV2
#print AKLT.Blueprint.H1.RationalEmbeddingEvaluationStatementV2
#print AKLT.Blueprint.H1.DifferenceStructureStatementV2

#check MvPolynomial.support_map_subset
#check MvPolynomial.eval_map
#check MvPolynomial.support_sub
#check MvPolynomial.C_mul'
#check Matrix.PosSemidef.kronecker
#check Matrix.PosSemidef.submatrix
#check Matrix.trace_kronecker
#check AKLT.Blueprint.H1.singlePauliTrace

#eval Fintype.card ((∅ : Finset (Fin 0)) → Fin 4)
#eval Fintype.card ((∅ : Finset (Fin 0)) → Fin 2)
#eval Fintype.card ((∅ : Finset (Fin 2)) → Fin 4)
#eval Fintype.card ((∅ : Finset (Fin 2)) → Fin 2)
