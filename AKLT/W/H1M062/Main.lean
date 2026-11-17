module
public import AKLT.Blueprint.H1.NodesV2Reduction

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section

namespace AKLT.W.H1M062

theorem main : AKLT.Blueprint.H1.RationalEmbeddingEvaluationStatementV2 := by
  intro p u
  simp [AKLT.Defs.evaluateRealPolynomial, AKLT.Defs.evaluateReduced,
    MvPolynomial.eval_map]

end AKLT.W.H1M062
