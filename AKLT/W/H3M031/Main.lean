module
public import AKLT.Blueprint.H3.NodesV2Stationary

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H3M031

theorem main : AKLT.Blueprint.H3.StationaryCoefficientOffCentreStatementV2 := by
  intro m q Q X d₀ φ a x d ψ hDestination
  simp [AKLT.Defs.stationaryCoefficientV2, AKLT.Defs.stationaryCoefficient,
    hDestination]

end AKLT.W.H3M031
