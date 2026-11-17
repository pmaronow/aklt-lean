module
public import AKLT.W.REC070.Regroup
public import AKLT.W.REC070.Increment

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-! The witness perturbation bound for the fixed cutoff-twelve kernel ordering.
The unshifted row bound is the numerical premise of the frozen statement. -/

namespace AKLT.W.REC070

/-- The same dyadic witness satisfies the shifted row bound within the explicit budget. -/
theorem main : AKLT.Blueprint.Rec.WitnessPerturbationStatement :=
  main_of_residuals rowExpansion_proved lengthIncrement_proved

end AKLT.W.REC070
