import AKLT.Blueprint.H3.NodesPrefix

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.H3M021

private theorem wordVertex_takeWord {n L : ℕ} (hLn : L ≤ n)
    (w : DirectionWord n) (j : ℕ) (hj : j ≤ L) :
    wordVertex kernelStart (takeWord w L) j = wordVertex kernelStart w j := by
  classical
  unfold wordVertex
  congr 1
  let s : Finset (Fin L) := Finset.univ.filter (fun i => i.val < j)
  let t : Finset (Fin n) := Finset.univ.filter (fun i => i.val < j)
  have hs : s ⊆ Finset.univ := Finset.filter_subset _ _
  have ht : t ⊆ Finset.univ := Finset.filter_subset _ _
  have hleft :
      (∑ i : Fin L, if i.val < j then (takeWord w L i).step else 0) =
        ∑ i ∈ s, (takeWord w L i).step := by
    rw [← Finset.sum_filter]
  have hright :
      (∑ i : Fin n, if i.val < j then (w i).step else 0) =
        ∑ i ∈ t, (w i).step := by
    rw [← Finset.sum_filter]
  rw [hleft, hright]
  apply Finset.sum_bij (fun i hi => ⟨i.val, by
    have hi' : i.val < j := (Finset.mem_filter.mp hi).2
    omega⟩)
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
  · intro i hi k hk heq
    have hval : i.val = k.val := congrArg (fun x : Fin n => x.val) heq
    apply Fin.ext
    exact hval
  · intro k hk
    have hkj : k.val < j := (Finset.mem_filter.mp hk).2
    refine ⟨⟨k.val, by omega⟩, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hk).2⟩
    · exact Fin.ext rfl
  · intro i hi
    have hij : i.val < j := (Finset.mem_filter.mp hi).2
    have hiL : i.val < L := lt_of_lt_of_le hij hj
    simp [takeWord, show i.val < n by omega]

private theorem takeWord_wordBond {n : ℕ} (hn : 12 ≤ n)
    (w : DirectionWord n) (i : Fin 12) :
    wordBond kernelStart (takeWord w 12) i =
      wordBond kernelStart w ⟨i.val, by omega⟩ := by
  have h0 := wordVertex_takeWord (n := n) (L := 12) hn w i.val (by omega)
  have h1 := wordVertex_takeWord (n := n) (L := 12) hn w (i.val + 1) (by omega)
  change {wordVertex kernelStart (takeWord w 12) i.val,
      wordVertex kernelStart (takeWord w 12) (i.val + 1)} =
    {wordVertex kernelStart w i.val, wordVertex kernelStart w (i.val + 1)}
  rw [h0, h1]

theorem main : AKLT.Blueprint.H3.LongTrailPrefixStatement := by
  intro X d₀ n hn w hclosed hfirst
  rcases hclosed with ⟨htrail, hterminal, hcentre, hfirstHit⟩
  rcases htrail with ⟨hinj, hinitial⟩
  rcases hfirst with ⟨i, hi0, hid⟩
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro i j hij
      have heq : wordBond kernelStart w ⟨i.val, by omega⟩ =
          wordBond kernelStart w ⟨j.val, by omega⟩ := by
        rw [← takeWord_wordBond (by omega) w i, ← takeWord_wordBond (by omega) w j]
        exact hij
      have hfin := hinj heq
      have hval : i.val = j.val := congrArg (fun x : Fin n => x.val) hfin
      apply Fin.ext
      exact hval
    · intro i hi
      have h := hinitial ⟨i.val, by omega⟩ hi
      simpa [takeWord, show i.val < n by omega] using h
  · refine ⟨⟨i.val, by omega⟩, hi0, ?_⟩
    simpa [takeWord, show i.val < n by omega] using hid
  · intro j hj
    have hvertex := wordVertex_takeWord (n := n) (L := 12) (by omega) w j hj
    constructor
    · rw [hvertex]
      exact hcentre j (by omega)
    · rw [hvertex]
      exact hfirstHit j (by omega)

end AKLT.W.H3M021
