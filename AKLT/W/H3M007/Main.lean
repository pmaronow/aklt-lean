module
public import AKLT.Blueprint.H3.NodesPhase

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.H3M007

private theorem takeWord_direction {n L : ℕ} (w : DirectionWord n) (hL : L ≤ n)
    (j : ℕ) (hj : j < L) : takeWord w L ⟨j, hj⟩ = w ⟨j, lt_of_lt_of_le hj hL⟩ := by
  simp [takeWord, Nat.lt_of_lt_of_le hj hL]

private theorem takeWord_vertex {n L : ℕ} (w : DirectionWord n) (hL : L ≤ n)
    (j : ℕ) (hj : j ≤ L) :
    wordVertex kernelStart (takeWord w L) j = wordVertex kernelStart w j := by
  unfold wordVertex
  congr 1
  rw [Finset.sum_fin_eq_sum_range, Finset.sum_fin_eq_sum_range]
  let fL : ℕ → Plane := fun k => if hk : k < L then
    if k < j then (takeWord w L ⟨k, hk⟩).step else 0 else 0
  let fN : ℕ → Plane := fun k => if hk : k < n then
    if k < j then (w ⟨k, hk⟩).step else 0 else 0
  change (∑ k ∈ Finset.range L, fL k) = ∑ k ∈ Finset.range n, fN k
  have hsmallL : (∑ k ∈ Finset.range L, fL k) = ∑ k ∈ Finset.range j, fL k := by
    symm
    apply Finset.sum_subset (Finset.range_mono hj)
    intro k hk hknot
    simp only [Finset.mem_range] at hk hknot
    have hkj : j ≤ k := Nat.le_of_not_lt hknot
    simp [fL, hk, not_lt.mpr hkj]
  have hsmallN : (∑ k ∈ Finset.range n, fN k) = ∑ k ∈ Finset.range j, fN k := by
    symm
    apply Finset.sum_subset (Finset.range_mono (le_trans hj hL))
    intro k hk hknot
    simp only [Finset.mem_range] at hk hknot
    have hkj : j ≤ k := Nat.le_of_not_lt hknot
    simp [fN, hk, not_lt.mpr hkj]
  rw [hsmallL, hsmallN]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_range] at hk
  have hkL : k < L := lt_of_lt_of_le hk hj
  have hkN : k < n := lt_of_lt_of_le hkL hL
  simp [fL, fN, hkL, hkN, hk, takeWord]

private theorem takeWord_departureCount {n L : ℕ} (w : DirectionWord n) (hL : L ≤ n)
    (i : Fin L) (z : Plane) :
    departureCount kernelStart (takeWord w L) i.val z = departureCount kernelStart w i.val z := by
  unfold departureCount
  have hiL : min i.val L = i.val := Nat.min_eq_left (Nat.le_of_lt i.isLt)
  have hin : min i.val n = i.val := Nat.min_eq_left (le_trans (Nat.le_of_lt i.isLt) hL)
  rw [hiL, hin]
  congr 1
  apply Finset.filter_congr
  intro j hj
  have hj' : j < i.val := Finset.mem_range.mp hj
  rw [takeWord_vertex w hL j (le_trans (Nat.le_of_lt hj') (Nat.le_of_lt i.isLt))]

private theorem takeWord_incoming {n L : ℕ} (w : DirectionWord n) (hL : L ≤ n)
    (i : Fin L) :
    wordIncoming kernelIncoming (takeWord w L) i = wordIncoming kernelIncoming w ⟨i.val, lt_of_lt_of_le i.isLt hL⟩ := by
  unfold wordIncoming
  split_ifs with h
  · rfl
  · apply takeWord_direction w hL

private theorem takeWord_revisit {n L : ℕ} (w : DirectionWord n) (hL : L ≤ n)
    (i : Fin L) :
    wordRevisit kernelStart (takeWord w L) i =
      wordRevisit kernelStart w ⟨i.val, lt_of_lt_of_le i.isLt hL⟩ := by
  unfold wordRevisit
  rw [takeWord_departureCount w hL i]
  rw [takeWord_vertex w hL i.val (Nat.le_of_lt i.isLt)]

private theorem takeWord_straight {n L : ℕ} (w : DirectionWord n) (hL : L ≤ n)
    (i : Fin L) :
    wordStraight kernelIncoming (takeWord w L) i =
      wordStraight kernelIncoming w ⟨i.val, lt_of_lt_of_le i.isLt hL⟩ := by
  simp [wordStraight, takeWord_direction w hL i.val i.isLt,
    takeWord_incoming w hL i]

private theorem takeWord_deadAt {n L : ℕ} (w : DirectionWord n) (hL : L ≤ n)
    (i : Fin L) (z : Plane) :
    deadAt (takeWord w L) i z = deadAt w ⟨i.val, lt_of_lt_of_le i.isLt hL⟩ z := by
  apply propext
  unfold deadAt
  rw [takeWord_departureCount w hL i z]

private theorem takeWord_responseNeighbours {n L : ℕ} (w : DirectionWord n) (hL : L ≤ n)
    (i : Fin L) :
    responseNeighbours (takeWord w L) i =
      responseNeighbours w ⟨i.val, lt_of_lt_of_le i.isLt hL⟩ := by
  simp [responseNeighbours, takeWord_vertex w hL i.val (Nat.le_of_lt i.isLt),
    takeWord_incoming w hL i]

private theorem takeWord_liveOtherNeighbours {n L : ℕ} (w : DirectionWord n) (hL : L ≤ n)
    (i : Fin L) :
    liveOtherNeighbours (takeWord w L) i =
      liveOtherNeighbours w ⟨i.val, lt_of_lt_of_le i.isLt hL⟩ := by
  classical
  unfold liveOtherNeighbours
  rw [takeWord_responseNeighbours w hL i]
  rw [takeWord_vertex w hL (i.val + 1) (by omega)]
  apply Finset.filter_congr
  intro z hz
  rw [takeWord_deadAt w hL i z]

private theorem takeWord_responsePairs {n L : ℕ} (w : DirectionWord n) (hL : L ≤ n)
    (i : Fin L) :
    responsePairs (takeWord w L) i =
      responsePairs w ⟨i.val, lt_of_lt_of_le i.isLt hL⟩ := by
  simp [responsePairs, takeWord_liveOtherNeighbours w hL i,
    takeWord_vertex w hL (i.val + 1) (by omega)]

private theorem takeWord_pairCoefficient {n L : ℕ} (w : DirectionWord n) (hL : L ≤ n)
    (i : Fin L) (p : Finset Plane) :
    pairCoefficient (takeWord w L) i p =
      pairCoefficient w ⟨i.val, lt_of_lt_of_le i.isLt hL⟩ p := by
  simp [pairCoefficient, takeWord_straight w hL i,
    takeWord_vertex w hL (i.val + 1) (by omega),
    takeWord_liveOtherNeighbours w hL i]

private theorem takeWord_witnessKappa {n L : ℕ} (w : DirectionWord n) (hL : L ≤ n)
    (i : Fin L) :
    witnessKappa (takeWord w L) i =
      witnessKappa w ⟨i.val, lt_of_lt_of_le i.isLt hL⟩ := by
  classical
  unfold witnessKappa
  rw [takeWord_responsePairs w hL i]
  apply Finset.sum_congr rfl
  intro p hp
  rw [takeWord_pairCoefficient w hL i p]

theorem main : AKLT.Blueprint.H3.PrefixCoefficientCausalityStatement := by
  intro n w L hL i φ ψ
  unfold truePhaseCoefficient
  rw [takeWord_revisit w hL i, takeWord_straight w hL i,
    takeWord_witnessKappa w hL i]

end AKLT.W.H3M007
