module
public import AKLT.W.REC096.Prefix
public import AKLT.W.REC096.Template

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC096

/-- Every live U departure in a stopped response-pair trail has a covered
template, with the shared internal-present-bond and one-sided tip matcher. -/
theorem main : AKLT.Blueprint.Rec.CoveredClosureStatementV2 := by
  intro p T n w ht i hU
  obtain ⟨hinv, hfuture⟩ := prefix_invariant p T w ht i.val (Nat.le_of_lt i.isLt)
  rw [arrival_eq p w i] at hinv
  have hp := hfuture i le_rfl
  have hyG := (Finset.mem_filter.mp hp.1).1
  rw [word_vertex_succ p.u w i.val i.isLt] at hp
  exact invariant_covered hinv hyG (ht.2.2.1 i.val i.isLt).2 hU hp

#print axioms main

end AKLT.W.REC096
