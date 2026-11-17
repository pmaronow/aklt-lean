module
public import AKLT.Blueprint.H1.NodesV2Pauli

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H1M060

theorem main : AKLT.Blueprint.H1.InversionBallStatementV2 := by
  intro n I u j
  by_cases hj : j ∈ I
  · simp [AKLT.Defs.invertVectorsReal, AKLT.Defs.normSq, AKLT.Defs.dot, hj]
  · simp [AKLT.Defs.invertVectorsReal, AKLT.Defs.normSq, AKLT.Defs.dot, hj]

end AKLT.W.H1M060

#print axioms AKLT.W.H1M060.main
