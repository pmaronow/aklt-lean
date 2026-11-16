import AKLT.Defs.OperatorContracts

namespace AKLT.Cert.H1
open AKLT.Defs

/-- A raw covered representative of exported effective pattern 0. -/
def smallPattern : PatternData where
  outgoing := .east
  status := fun x =>
    if x.val = (0, 0) ∨ x.val ∈ templateTips then .U
    else if x.val = (1, 0) ∨ x.val = (1, -1) then .D else .X
  kept := fun x =>
    if x.val = (0, 0) then {.east, .north, .west}
    else if x.val = (1, 0) then {.west, .south}
    else if x.val = (1, -1) then {.north, .east} else ∅

theorem smallPattern_covered : smallPattern.Covered := by
  unfold PatternData.Covered
  have ht : templateSites = {(0,0), (1,0), (-1,0), (0,1), (0,-1),
      (2,0), (-2,0), (0,2), (0,-2), (1,1), (-1,1), (-1,-1), (1,-1)} := by decide +kernel
  have hi : templateSites \ templateTips =
      {(0,0), (1,0), (-1,0), (0,1), (0,-1), (1,1), (-1,1), (-1,-1), (1,-1)} := by decide +kernel
  rw [hi]
  simp only [ht, templateCorners, templateTips, Finset.forall_mem_insert,
    Finset.mem_singleton, forall_eq]
  repeat' apply And.intro
  all_goals decide +kernel

theorem smallPattern_bonds : smallPattern.bonds =
    {((0, 0), (1, 0)), ((1, -1), (1, 0))} := by
  decide +kernel

#print axioms smallPattern_covered
#print axioms smallPattern_bonds
end AKLT.Cert.H1
