import AKLT.Blueprint.H1.NodesV2Reduction

noncomputable section

namespace AKLT.W.H1M062

theorem main : AKLT.Blueprint.H1.RationalEmbeddingEvaluationStatementV2 := by
  intro p u
  simp [AKLT.Defs.evaluateRealPolynomial, AKLT.Defs.evaluateReduced,
    MvPolynomial.eval_map]

end AKLT.W.H1M062
