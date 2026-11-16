import AKLT.Blueprint.H1.NodesV2Reduction

noncomputable section
open AKLT.Defs AKLT.Blueprint.H1

namespace AKLT.W.H1M064

/-- `c:reduce`: evaluation of the real-coefficient difference agrees with
the current evaluation minus the real threshold times the next evaluation. -/
theorem main : AKLT.Blueprint.H1.DifferenceEvaluationStatementV2 := by
  intro π r c u
  simp [AKLT.Defs.evaluateRealPolynomial, AKLT.Defs.reducedDifferenceReal,
    AKLT.Defs.reducedPolynomialReal, AKLT.Defs.evaluateReduced]

end AKLT.W.H1M064

#print axioms AKLT.W.H1M064.main
