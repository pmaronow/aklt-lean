module
public import AKLT.W.REC011.Comparison

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open AKLT.Defs

namespace AKLT.W.REC011

/-- The free partition decreases under a trace step. The quotient convention
also gives the bound when the original partition is zero. -/
theorem main : AKLT.Blueprint.Rec.FreeRatioUpperStatement := by
  intro a
  change (traceStep a.D a.y a.o).partition a.τ false (fun _ => 1) /
    a.D.partition a.τ false (fun _ => 1) ≤ 1
  have hp := freePartition_nonneg a.D a.τ
  have hcompare := freePartition_traceStep_le a.D a.τ a.y a.o
  by_cases hp0 : a.D.partition a.τ false (fun _ => 1) = 0
  · simp [hp0]
  · apply (div_le_iff₀ (lt_of_le_of_ne hp (Ne.symm hp0))).2
    simpa only [one_mul] using hcompare

end AKLT.W.REC011

#print axioms AKLT.W.REC011.main
