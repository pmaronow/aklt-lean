import AKLT.Blueprint.Q.NodesSplits
import AKLT.Uniq.BondAlgebra

namespace AKLT.W.Q032

theorem main : AKLT.Blueprint.Q.DeterminantPrimeEmbeddingStatement := by
  intro _ L N e
  exact AKLT.Uniq.singletPrime L N e

#print axioms main

end AKLT.W.Q032
