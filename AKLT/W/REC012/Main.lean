module
public import AKLT.W.REC012.Comparison

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC012

/-- The pinned step ratio is at most 12/5. The partition inequality also
covers a zero normalizer, for which Lean's real division is zero. -/
theorem main : AKLT.Blueprint.Rec.PinnedRatioUpperStatement := by
  intro a
  let z := a.D.partition a.τ true (fun _ => 1)
  have hz : 0 ≤ z := network_partition_nonneg a.D a.τ true
  have hnum := pinned_partition_upper a
  change (traceStep a.D a.y a.o).partition a.τ true (fun _ => 1) / z ≤ 12 / 5
  by_cases hzero : z = 0
  · simp [hzero]
    norm_num
  · have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hzero)
    exact (div_le_iff₀ hzpos).2 (by simpa [z] using hnum)

end AKLT.W.REC012
