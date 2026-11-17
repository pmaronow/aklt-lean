module
public import AKLT.W.H3C026.Assembly
public import AKLT.W.H3C026.KnownMask
public import AKLT.W.H3C026.DeadMask
public import AKLT.W.H3C026.Pull

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H3C026

/-- The packed production row is exactly the corrected stationary integer row. -/
theorem main : CertData.H3.Bridge.RowTermsV2Leaf :=
  rowTermsV2_from_leaves ordinaryMask_proved knownMask_proved deadMask_proved pull_proved

end AKLT.W.H3C026

#print axioms AKLT.W.H3C026.main
