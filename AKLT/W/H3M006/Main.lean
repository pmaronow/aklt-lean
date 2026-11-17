module
public import AKLT.Blueprint.H3.NodesPhase

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.H3

namespace AKLT.W.H3M006

private lemma prefix_toFinset_of_pairwise {n : ℕ} (l : List (Fin n))
    (hp : l.Pairwise (fun a b => a.val < b.val)) (j : Fin n) (hj : j ∈ l) :
    (l.take (l.idxOf j + 1)).toFinset =
      l.toFinset.filter (fun i => i.val ≤ j.val) := by
  ext i
  simp only [Finset.mem_filter, List.mem_toFinset]
  constructor
  · intro hit
    have him : i ∈ l := List.mem_of_mem_take hit
    have htake := (List.mem_take_iff_idxOf_lt him).mp hit
    have hpos : l.idxOf i ≤ l.idxOf j := by omega
    have hi' := List.idxOf_lt_length_iff.mpr him
    have hj' := List.idxOf_lt_length_iff.mpr hj
    have hval : i.val ≤ j.val := by
      by_cases heq : l.idxOf i = l.idxOf j
      ·
        have hgeti : l.get ⟨l.idxOf i, hi'⟩ = i := List.idxOf_get hi'
        have hgetj : l.get ⟨l.idxOf j, hj'⟩ = j := List.idxOf_get hj'
        have : i = j := by
          have hEq : (⟨l.idxOf i, hi'⟩ : Fin l.length) = ⟨l.idxOf j, hj'⟩ :=
            Fin.ext heq
          have h := congrArg (fun k : Fin l.length => l.get k) hEq
          simpa [hgeti, hgetj] using h
        simp [this]
      · have hlt : l.idxOf i < l.idxOf j := by omega
        have hpos : (⟨l.idxOf i, hi'⟩ : Fin l.length) < ⟨l.idxOf j, hj'⟩ :=
          Fin.mk_lt_mk.mpr hlt
        have hltval := hp.rel_get_of_lt hpos
        exact Nat.le_of_lt (by simpa [List.idxOf_get hi', List.idxOf_get hj'] using hltval)
    exact ⟨him, hval⟩
  · rintro ⟨him, hval⟩
    have hidx : l.idxOf i ≤ l.idxOf j := by
      by_contra hn
      have hlt : l.idxOf j < l.idxOf i := by omega
      have hi' := List.idxOf_lt_length_iff.mpr him
      have hj' := List.idxOf_lt_length_iff.mpr hj
      have hpos : (⟨l.idxOf j, hj'⟩ : Fin l.length) < ⟨l.idxOf i, hi'⟩ :=
        Fin.mk_lt_mk.mpr hlt
      have hltval := hp.rel_get_of_lt hpos
      rw [List.idxOf_get hj', List.idxOf_get hi'] at hltval
      omega
    exact (List.mem_take_iff_idxOf_lt him).mpr (by omega)

private lemma finRange_pairwise_lt (n : ℕ) :
    (List.finRange n).Pairwise (fun a b => a.val < b.val) := by
  simp [List.pairwise_iff_getElem]

private lemma filter_finRange_pairwise_lt {n : ℕ} (p : Fin n → Bool) :
    ((List.finRange n).filter p).Pairwise (fun a b => a.val < b.val) := by
  exact (finRange_pairwise_lt n).filter p

theorem main : AKLT.Blueprint.H3.LongOrderingMultiplierStatement := by
  classical
  intro n w
  let F : List (Fin n) := List.finRange n
  let P : Fin n → Bool := fun i => !wordRevisit kernelStart w i
  let S : List (Fin n) := F.filter (fun i => P i && wordStraight kernelIncoming w i)
  let T : List (Fin n) := F.filter (fun i => P i && !wordStraight kernelIncoming w i)
  have hfirst : firstVisitList w = F.filter P := by
    simp [F, P, firstVisitList]
  have hS : (firstVisitList w).filter (wordStraight kernelIncoming w) = S := by
    rw [hfirst]
    simp [S, P, F, Bool.and_comm]
  have hT : (firstVisitList w).filter (fun i => !wordStraight kernelIncoming w i) = T := by
    rw [hfirst]
    simp [T, P, F, Bool.and_comm]
  have horder : longOrdering w = S ++ T := by
    simp [longOrdering, hS, hT]
  have hnodupS : S.Nodup := by
    apply List.Nodup.filter
    exact List.nodup_finRange n
  have hnodupT : T.Nodup := by
    apply List.Nodup.filter
    exact List.nodup_finRange n
  have hcross : ∀ a ∈ S, ∀ b ∈ T, a ≠ b := by
    intro a ha b hb hab
    subst b
    simp only [S, T, List.mem_filter] at ha hb
    have hs : wordStraight kernelIncoming w a = true :=
      (Bool.and_eq_true_iff.mp ha.2).2
    have hnot : (!wordStraight kernelIncoming w a) = true :=
      (Bool.and_eq_true_iff.mp hb.2).2
    have ht : wordStraight kernelIncoming w a = false := by
      cases h : wordStraight kernelIncoming w a <;> simp_all
    simp [hs] at ht
  have hnodup : (S ++ T).Nodup := List.nodup_append.mpr ⟨hnodupS, hnodupT, hcross⟩
  have hpairS : S.Pairwise (fun a b => a.val < b.val) := by
    simpa [S, F, P] using
      (filter_finRange_pairwise_lt (n := n) (fun i => !wordRevisit kernelStart w i &&
        wordStraight kernelIncoming w i))
  have hpairT : T.Pairwise (fun a b => a.val < b.val) := by
    simpa [T, F, P] using
      (filter_finRange_pairwise_lt (n := n) (fun i => !wordRevisit kernelStart w i &&
        !wordStraight kernelIncoming w i))
  refine ⟨?_, ?_, ?_⟩
  · rw [horder]
    exact hnodup
  · rw [horder, List.toFinset_append]
    ext i
    simp only [Finset.mem_union, List.mem_toFinset,
      Finset.mem_filter, Finset.mem_univ, true_and]
    cases hs : wordStraight kernelIncoming w i <;> simp [S, T, F, P, hs]
  · intro j hj
    rw [horder] at hj
    have hstraight : wordStraight kernelIncoming w j = true ∨
        wordStraight kernelIncoming w j = false := by cases wordStraight kernelIncoming w j <;> simp
    rcases hstraight with hs | ht
    · have hjS : j ∈ S := by
        rcases List.mem_append.mp hj with h | h
        · exact h
        · simp [T, hs] at h
      have hjT : j ∉ T := by
        simp [T, hs]
      have hidx : (S ++ T).idxOf j = S.idxOf j := List.idxOf_append_of_mem hjS
      have hbound : S.idxOf j + 1 ≤ S.length := by
        have := List.idxOf_lt_length_iff.mpr hjS
        omega
      have htake : (S ++ T).take ((S ++ T).idxOf j + 1) = S.take (S.idxOf j + 1) := by
        rw [hidx, List.take_append_of_le_length hbound]
      have hprefix := prefix_toFinset_of_pairwise S hpairS j hjS
      have hset : S.toFinset.filter (fun i => i.val ≤ j.val) =
          Finset.univ.filter (fun i => wordRevisit kernelStart w i = false ∧
            wordStraight kernelIncoming w i = true ∧ i.val ≤ j.val) := by
        ext i
        simp [S, F, P, Finset.filter_filter]
        simp only [and_assoc]
      rw [horder, orderedMultiplier, htake,
        ← List.prod_toFinset (fun i => passageFactor (wordStraight kernelIncoming w i))
          (hnodupS.sublist (List.take_sublist _ _))]
      rw [hprefix, hset]
      simp [longMultiplier, hs, Finset.prod_filter]
    · have hjT : j ∈ T := by
        rcases List.mem_append.mp hj with h | h
        · simp [S, ht] at h
        · exact h
      have hjS : j ∉ S := by
        simp [S, ht]
      have hidx : (S ++ T).idxOf j = S.length + T.idxOf j :=
        List.idxOf_append_of_notMem hjS
      have hbound : S.length ≤ S.length + T.idxOf j + 1 := by omega
      have htake : (S ++ T).take ((S ++ T).idxOf j + 1) =
          S ++ T.take (T.idxOf j + 1) := by
        rw [hidx]
        have hlen : S.length + T.idxOf j + 1 =
            S.length + (T.idxOf j + 1) := by omega
        rw [hlen, List.take_add]
        simp
      have hprefix := prefix_toFinset_of_pairwise T hpairT j hjT
      have hdisjSet : Disjoint S.toFinset (T.toFinset.filter (fun i => i.val ≤ j.val)) := by
        rw [Finset.disjoint_left]
        intro i hiS hiT
        simp [S, T, F, P] at hiS hiT
        simp_all
      have hset : S.toFinset ∪ T.toFinset.filter (fun i => i.val ≤ j.val) =
          Finset.univ.filter (fun i => wordRevisit kernelStart w i = false ∧
            (wordStraight kernelIncoming w i = true ∨ i.val ≤ j.val)) := by
        ext i
        by_cases hs : wordStraight kernelIncoming w i = true
        · simp [S, T, F, P, hs]
        · simp [S, T, F, P, hs]
      rw [horder, orderedMultiplier, htake, List.map_append, List.prod_append,
        ← List.prod_toFinset (fun i => passageFactor (wordStraight kernelIncoming w i)) hnodupS,
        ← List.prod_toFinset (fun i => passageFactor (wordStraight kernelIncoming w i))
          (hnodupT.sublist (List.take_sublist _ _))]
      rw [hprefix, ← Finset.prod_union hdisjSet, hset]
      simp [longMultiplier, ht, Finset.prod_filter]

end AKLT.W.H3M006
