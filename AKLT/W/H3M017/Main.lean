module
public import AKLT.Blueprint.H3.NodesDomination
public import AKLT.Cert.H2.Words

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

open AKLT.Defs

namespace AKLT.W.H3M017

theorem main : AKLT.Blueprint.H3.ClosedTrailStepGeometryStatement := by
  intro X n w hClosed i
  rcases hClosed with ⟨_, _, hCenter, hTarget⟩
  have hi : i.val < n := i.isLt
  have hStep := AKLT.Cert.H2.vertex_succ kernelStart w i.val hi
  refine ⟨hStep, hCenter i.val (by omega), hTarget i.val hi, ?_⟩
  exact hCenter (i.val + 1) (by omega)

end AKLT.W.H3M017

#print axioms AKLT.W.H3M017.main
