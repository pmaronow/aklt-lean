import AKLT.Blueprint.Rec.NodesV2Ordering

open AKLT.Defs

namespace AKLT.W.REC101

theorem main : AKLT.Blueprint.Rec.LongKernelOrderingStatementV2 := by
  intro n X w _ hn
  have hfin : (List.finRange n).Pairwise (fun i j : Fin n => i.val < j.val) := by
    rw [← List.ofFn_id n, List.pairwise_ofFn]
    intro i j hij
    exact Fin.lt_def.mp hij
  have hfirst : (firstVisitList w).Pairwise (fun i j : Fin n => i.val < j.val) := by
    unfold firstVisitList
    exact hfin.filter _
  refine ⟨?_, ?_, ?_⟩
  · simp [kernelOrdering, longOrdering, Nat.not_le.mpr (by omega)]
  · exact hfirst.filter _
  · exact hfirst.filter _

end AKLT.W.REC101
