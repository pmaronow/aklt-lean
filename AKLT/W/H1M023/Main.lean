import AKLT.W.H1M023.Degree

namespace AKLT.W.H1M023

/-- Leaf `c:reduce`: reduction preserves separate internal degree at most four
and removes all internal variables outside the retained spin sites. -/
theorem main : AKLT.Blueprint.H1.ReducedDegreeStatement := by
  intro π _ r next
  exact reducedIntegrand_admissible π r next

#print axioms main

end AKLT.W.H1M023
