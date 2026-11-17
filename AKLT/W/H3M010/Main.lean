module
public import AKLT.Blueprint.H3.NodesDomination

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs
open AKLT.Blueprint.H3

namespace AKLT.W.H3M010

private theorem wordVertex_succ {n : ℕ} (u : Plane) (w : DirectionWord n)
    (j : ℕ) (hj : j < n) :
    wordVertex u w (j + 1) = wordVertex u w j + (w ⟨j, hj⟩).step := by
  simp only [wordVertex, Nat.lt_succ_iff]
  have hs : (∑ i : Fin n, if i.val ≤ j then (w i).step else 0) =
      (∑ i : Fin n, if i.val < j then (w i).step else 0) + (w ⟨j, hj⟩).step := by
    calc
      _ = ∑ i : Fin n, ((if i.val < j then (w i).step else 0) +
          (if i = ⟨j, hj⟩ then (w i).step else 0)) := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases he : i.val = j
        · have hifin : i = ⟨j, hj⟩ := Fin.ext he
          simp [he, hifin]
        · by_cases hlt : i.val < j
          · have hneq : i ≠ ⟨j, hj⟩ := by
              intro h
              apply he
              exact congrArg Fin.val h
            simp [hlt, hneq] <;> omega
          · have hgt : j < i.val := by omega
            have hnotle : ¬ i.val ≤ j := by omega
            have hneq : i ≠ ⟨j, hj⟩ := by
              intro h
              apply he
              exact congrArg Fin.val h
            simp [hlt, hnotle, hneq]
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
        simp
  rw [hs]
  simp [add_assoc]

private theorem suffixWindow_get {n : ℕ} (w : DirectionWord n) (j : ℕ)
    (hj : 10 ≤ j) (hjn : j ≤ n) (k : Fin 10) :
    suffixWindow w j k = w ⟨j - 10 + k.val, by omega⟩ := by
  have hltj : j - 10 + k.val < j := by omega
  have hltn : j - 10 + k.val < n := by omega
  simp [suffixWindow, lastWindowWord, takeWord, hltj, hltn]

private theorem suffixVertex_translate {n : ℕ} (w : DirectionWord n) (j : ℕ)
    (hj : 10 ≤ j) (hjn : j ≤ n) :
    ∀ k ≤ 10,
      wordVertex (0, 0) (suffixWindow w j) k +
        wordVertex kernelStart w (j - 10) =
        wordVertex kernelStart w (j - 10 + k) := by
  intro k hk
  induction k with
  | zero =>
      simp [wordVertex]
  | succ k ih =>
      have hklt : k < 10 := by omega
      have hseg : j - 10 + k < n := by omega
      have hget := suffixWindow_get w j hj hjn ⟨k, hklt⟩
      have hget' : suffixWindow w j ⟨k, hklt⟩ = w ⟨j - 10 + k, hseg⟩ := by
        simpa using hget
      have hidx : j - 10 + (k + 1) = (j - 10 + k) + 1 := by omega
      rw [wordVertex_succ (0, 0) (suffixWindow w j) k hklt]
      rw [hidx]
      rw [wordVertex_succ kernelStart w (j - 10 + k) hseg]
      rw [hget']
      have hih := ih (by omega)
      calc
        (wordVertex (0, 0) (suffixWindow w j) k + (w ⟨j - 10 + k, hseg⟩).step) +
            wordVertex kernelStart w (j - 10) =
          (wordVertex (0, 0) (suffixWindow w j) k +
            wordVertex kernelStart w (j - 10)) + (w ⟨j - 10 + k, hseg⟩).step := by abel
        _ = wordVertex kernelStart w (j - 10 + k) + (w ⟨j - 10 + k, hseg⟩).step := by rw [hih]

private theorem rememberedRevisit_implies_true {n : ℕ} (w : DirectionWord n)
    (i : Fin n) (hi : 10 ≤ i.val) :
    0 < departureCount (0, 0) (suffixWindow w i.val) 10
      (wordVertex (0, 0) (suffixWindow w i.val) 10) →
    0 < departureCount kernelStart w i.val (wordVertex kernelStart w i.val) := by
  intro hwindow
  have hcard : 0 <
      (((Finset.range 10).filter fun j =>
        wordVertex (0, 0) (suffixWindow w i.val) j =
          wordVertex (0, 0) (suffixWindow w i.val) 10).card) := by
    simpa [departureCount] using hwindow
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hcard
  rcases Finset.mem_filter.mp hj with ⟨hjrange, heq⟩
  have hjlt : j < 10 := Finset.mem_range.mp hjrange
  have htransj := suffixVertex_translate w i.val hi (Nat.le_of_lt i.isLt) j (by omega)
  have htrans10 := suffixVertex_translate w i.val hi (Nat.le_of_lt i.isLt) 10 (by omega)
  have hwhole : wordVertex kernelStart w (i.val - 10 + j) =
      wordVertex kernelStart w (i.val - 10 + 10) := by
    have h := congrArg (fun z : Plane => z + wordVertex kernelStart w (i.val - 10)) heq
    rw [htransj, htrans10] at h
    exact h
  have hiidx : i.val - 10 + 10 = i.val := by omega
  have hwhole' : wordVertex kernelStart w (i.val - 10 + j) =
      wordVertex kernelStart w i.val := by simpa [hiidx] using hwhole
  have hmem : (Finset.range (min i.val n)).filter
      (fun k => wordVertex kernelStart w k = wordVertex kernelStart w i.val) |>.Nonempty := by
    refine ⟨i.val - 10 + j, Finset.mem_filter.mpr ⟨?_, hwhole'⟩⟩
    rw [Finset.mem_range]
    omega
  have hpos := Finset.card_pos.mpr hmem
  simpa [departureCount, Nat.min_eq_left (Nat.le_of_lt i.isLt)] using hpos

/-- The last-ten-letter state updates by one departure and remembers the actual incoming edge. -/
theorem main : AKLT.Blueprint.H3.SuffixWindowLabelsStatement := by
  intro n w hw i hi
  have hin : i.val < n := i.isLt
  have hnextle : i.val + 1 ≤ n := by omega
  have harrival : windowArrival (suffixWindow w i.val) =
      wordIncoming kernelIncoming w i := by
    have hget := suffixWindow_get w i.val hi (Nat.le_of_lt hin) ⟨9, by omega⟩
    simp only [windowArrival]
    rw [dif_pos (by omega), hget]
    have hi0 : i.val ≠ 0 := by omega
    simp only [wordIncoming, dif_neg hi0]
    apply congrArg w
    apply Fin.ext
    simp
    omega
  refine ⟨?_, harrival, ?_, ?_⟩
  · funext k
    by_cases hk : k.val + 1 < 10
    · simp only [windowSuccessor, dif_pos hk]
      have hleft := suffixWindow_get w i.val hi (Nat.le_of_lt hin) ⟨k.val + 1, hk⟩
      have hright := suffixWindow_get w (i.val + 1) (by omega) hnextle k
      rw [hleft, hright]
      apply congrArg w
      apply Fin.ext
      simp
      omega
    · have hkval : k.val = 9 := by omega
      have hkfin : k = ⟨9, by omega⟩ := Fin.ext hkval
      rw [hkfin]
      simp only [windowSuccessor, dif_neg (by omega)]
      have hright := suffixWindow_get w (i.val + 1) (by omega) hnextle ⟨9, by omega⟩
      rw [hright]
      apply congrArg w
      apply Fin.ext
      simp
      omega
  · intro hkind
    by_cases hc : 0 < departureCount (0, 0) (suffixWindow w i.val) 10
        (wordVertex (0, 0) (suffixWindow w i.val) 10)
    · have htrue := rememberedRevisit_implies_true w i hi hc
      simp [wordRevisit, htrue]
    · by_cases he : w i = windowArrival (suffixWindow w i.val)
      · simp [windowKind, hc, he] at hkind
      · simp [windowKind, hc, he] at hkind
  · intro hnotrev
    have htrueNo : ¬ 0 < departureCount kernelStart w i.val
        (wordVertex kernelStart w i.val) := by
      have hd : decide (0 < departureCount kernelStart w i.val
          (wordVertex kernelStart w i.val)) = false := by
        simpa [wordRevisit] using hnotrev
      exact of_decide_eq_false hd
    have hwindowNo : ¬ 0 < departureCount (0, 0) (suffixWindow w i.val) 10
        (wordVertex (0, 0) (suffixWindow w i.val) 10) := by
      intro hc
      exact htrueNo (rememberedRevisit_implies_true w i hi hc)
    have hwindowZero : departureCount (0, 0) (suffixWindow w i.val) 10
        (wordVertex (0, 0) (suffixWindow w i.val) 10) = 0 := by omega
    simp [windowKind, trueKind, hwindowZero, hnotrev, wordStraight, harrival]

end AKLT.W.H3M010
