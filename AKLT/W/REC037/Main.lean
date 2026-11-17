module
public import AKLT.W.REC037.Contract

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.REC037

/-- The degree-three U-step identity from `l:stepid`. -/
theorem main : AKLT.Blueprint.Rec.UStepMomentStatement := uStepMoment

end AKLT.W.REC037
