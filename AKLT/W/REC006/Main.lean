import AKLT.W.REC006.Positivity

noncomputable section
open AKLT.Defs

namespace AKLT.W.REC006

/-- Free positivity for the pair inserted after removing the departure site. -/
theorem main : AKLT.Blueprint.Rec.FreeRemovedPairStatement := by
  intro a f _ g _ _
  exact free_pair_mean_nonneg (removeSite a.D a.y) a.τ f g

#print axioms main

end AKLT.W.REC006
