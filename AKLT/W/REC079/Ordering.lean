import AKLT.W.REC079.TraceStatus

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs AKLT.Blueprint.Rec AKLT.Cert.H2

namespace AKLT.W.REC079

/-- The adopted ordering enumerates precisely the lattice first visits. The
short score order and long phase order are kept in their original scopes. -/
theorem kernelOrdering_perm {n : ℕ} (w : DirectionWord n) :
    (kernelOrdering w).Perm (firstVisitList w) := by
  unfold kernelOrdering
  split_ifs
  · exact List.mergeSort_perm _ _
  · exact List.filter_append_perm _ _

theorem firstVisitList_nodup {n : ℕ} (w : DirectionWord n) : (firstVisitList w).Nodup :=
  (List.nodup_finRange n).filter _

theorem kernelOrdering_nodup {n : ℕ} (w : DirectionWord n) : (kernelOrdering w).Nodup :=
  (kernelOrdering_perm w).nodup_iff.mpr (firstVisitList_nodup w)

theorem kernelOrdering_mem_iff {n : ℕ} (w : DirectionWord n) (i : Fin n) :
    i ∈ kernelOrdering w ↔ wordRevisit kernelStart w i = false := by
  rw [(kernelOrdering_perm w).mem_iff]
  simp [firstVisitList]

/-- In particular the restricted true-U ordering is a repetition-free sublist
of the SAME fixed kernel order used in every budget. -/
theorem U_departure_mem_ordering (p : PairData) {n : ℕ} (w : DirectionWord n) (i : Fin n)
    (hU : (prefixNetwork p.normalized p.u w i.val).status (wordVertex p.u w i.val) = .U) :
    i ∈ kernelOrdering (canonicalWord p w) :=
  (kernelOrdering_mem_iff _ _).mpr (U_departure_canonical_first_visit p w i hU)

/-- Each of the two filters in the LONG order preserves increasing path
indices. This assertion is not applied to the short rational-score order. -/
theorem long_filters_path_order {n : ℕ} (w : DirectionWord n) :
    ((firstVisitList w).filter (wordStraight kernelIncoming w)).Pairwise
        (fun i j => i.val < j.val) ∧
      ((firstVisitList w).filter (fun i => !wordStraight kernelIncoming w i)).Pairwise
        (fun i j => i.val < j.val) := by
  have h : (firstVisitList w).Pairwise (fun i j => i.val < j.val) :=
    (List.pairwise_lt_finRange n).filter _
  exact ⟨h.filter _, h.filter _⟩

/-- The short branch retains its exact rational sort, while only the long
branch uses the straight-first concatenation. -/
theorem kernelOrdering_scopes {n : ℕ} (w : DirectionWord n) :
    (n ≤ 12 → kernelOrdering w = (firstVisitList w).mergeSort (shortOrderLE w)) ∧
      (12 < n → kernelOrdering w =
        (firstVisitList w).filter (wordStraight kernelIncoming w) ++
          (firstVisitList w).filter (fun i => !wordStraight kernelIncoming w i)) := by
  constructor
  · intro hn; simp only [kernelOrdering, ite_eq_left hn]
  · intro hn; simp only [kernelOrdering, ite_eq_right (by omega : ¬n ≤ 12)]

end AKLT.W.REC079
