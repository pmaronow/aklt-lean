import AKLT.Blueprint.Rec.NodesKernel

noncomputable section

namespace AKLT.W.REC060

private theorem append_cons_perm {α : Type*} (a : α) (l₁ l₂ : List α) :
    (l₁ ++ a :: l₂).Perm (a :: l₁ ++ l₂) := by
  induction l₁ with
  | nil => simp
  | cons b l ih =>
      exact (List.Perm.cons b ih).trans (List.Perm.swap a b (l ++ l₂))

private theorem filter_partition_perm {α : Type*} (l : List α) (p : α → Bool) :
    (l.filter p ++ l.filter (fun x => !p x)).Perm l := by
  induction l with
  | nil => simp
  | cons a l ih =>
      cases h : p a
      · have h' : p a = false := h
        simpa [h'] using
          (append_cons_perm a (l.filter p) (l.filter (fun x => !p x))).trans
            (List.Perm.cons a ih)
      · have h' : p a = true := h
        simpa [h'] using List.Perm.cons a ih

theorem firstVisitList_nodup {n : ℕ} (w : AKLT.Defs.DirectionWord n) :
    (AKLT.Defs.firstVisitList w).Nodup := by
  unfold AKLT.Defs.firstVisitList
  exact List.Nodup.filter _ (List.nodup_finRange n)

theorem main : AKLT.Blueprint.Rec.KernelOrderingStatement := by
  intro n w
  have hfirst : (AKLT.Defs.firstVisitList w).Nodup := firstVisitList_nodup w
  have hperm : (AKLT.Defs.kernelOrdering w).Perm (AKLT.Defs.firstVisitList w) := by
    unfold AKLT.Defs.kernelOrdering
    split
    · exact List.mergeSort_perm _ _
    · exact filter_partition_perm _ _
  exact ⟨hperm, hperm.nodup_iff.mpr hfirst⟩

end AKLT.W.REC060
