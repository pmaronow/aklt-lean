import AKLT.Blueprint.H1.NodesV2Reduction

noncomputable section
open AKLT.Defs

namespace AKLT.W.H1M061

theorem main : AKLT.Blueprint.H1.RationalEmbeddingStructureStatementV2 := by
  intro p J hp hs
  constructor
  · intro m hm j
    have hm' : m ∈ p.support := MvPolynomial.support_map_subset _ _ hm
    exact hp m hm' j
  · intro m hm j hj k
    have hm' : m ∈ p.support := MvPolynomial.support_map_subset _ _ hm
    exact hs m hm' j hj k

#print axioms main

end AKLT.W.H1M061
