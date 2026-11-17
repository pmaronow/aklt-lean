module
public import AKLT.Blueprint.Q.NodesSplits
public import AKLT.Uniq.BondAlgebra

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.Q032

theorem main : AKLT.Blueprint.Q.DeterminantPrimeEmbeddingStatement := by
  intro _ L N e
  exact AKLT.Uniq.singletPrime L N e

#print axioms main

end AKLT.W.Q032
