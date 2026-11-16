import AKLT.W.H1C009.Groups

namespace AKLT.W.H1C009
open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

theorem presentBond_symm (π : PatternData) (x y : Plane) :
    presentBond π x y = presentBond π y x := by
  simp only [presentBond, or_comm]

theorem input_left (a : Input) (ha : inputCheck a = true) (i : Nat) (hi : i < 8) :
    (inputSpec a i).left = presentBond (inputPattern a)
      (ringSites.getD ((i+7)%8) (0,0)) (ringSites.getD i (0,0)) := by
  have h := (raw_edge a ha (4+(i+7)%8) (by omega)).symm
  have he : templateEdges.getD (4+(i+7)%8) ((0,0),(0,0)) =
      (ringSites.getD ((i+7)%8) (0,0), ringSites.getD i (0,0)) := by
    interval_cases i <;> simp [templateEdges, ringSites]
  rw [he] at h
  exact h

theorem input_right (a : Input) (ha : inputCheck a = true) (i : Nat) (hi : i < 8) :
    (inputSpec a i).right = presentBond (inputPattern a)
      (ringSites.getD i (0,0)) (ringSites.getD ((i+1)%8) (0,0)) := by
  have h := (raw_edge a ha (4+i) (by omega)).symm
  have he : templateEdges.getD (4+i) ((0,0),(0,0)) =
      (ringSites.getD i (0,0), ringSites.getD ((i+1)%8) (0,0)) := by
    interval_cases i <;> simp [templateEdges, ringSites]
  rw [he] at h
  exact h

theorem input_center (a : Input) (ha : inputCheck a = true) (i : Nat) (hi : i < 8) :
    (inputSpec a i).center = presentBond (inputPattern a) (ringSites.getD i (0,0)) (0,0) := by
  by_cases hp : i%2 = 0
  · have h := (raw_edge a ha (i/2) (by omega)).symm
    have he : templateEdges.getD (i/2) ((0,0),(0,0)) =
        ((0,0),ringSites.getD i (0,0)) := by
      interval_cases i <;> simp_all [templateEdges, ringSites]
    rw [he, presentBond_symm] at h
    simpa only [inputSpec, hp, beq_self_eq_true, Bool.true_and] using h
  · simp only [inputSpec, show (i%2 == 0) = false by simp [hp], Bool.false_and]
    simp only [presentBond, PatternData.bonds, internalBonds_explicit]
    interval_cases i <;> simp_all [ringSites, internalTemplateEdges]

theorem input_diluted (a : Input) (i : Nat) (hi : i < 8) :
    (inputSpec a i).diluted = decide ((inputPattern a).statusAt (ringSites.getD i (0,0)) = .D) := by
  apply Bool.eq_iff_iff.mpr
  simp only [inputSpec, beq_iff_eq, decide_eq_true_eq, statusAt_ring_diluted a i hi]

theorem inputSlots_even (a : Input) (i : Nat) (he : i%2 = 0) :
    inputSlots a i = 0 ∨ inputSlots a i = 1 := by
  unfold inputSlots
  simp only [he, beq_self_eq_true, ite_true]
  cases (rawEdges a.axes a.corners).getD (12+i/2) false <;> simp

/-- A tip has at most one slot, so its dimension never uses the adjacent axial status. -/
theorem input_dim (a : Input) (ha : inputCheck a = true) (i : Nat) (hi : i < 8) :
    inputDimension a i = groupDim (inputPattern a) (inputRepresentation a) (groupPoint i) := by
  unfold inputDimension groupDim
  rw [← inputSlots_eq a ha i hi]
  by_cases he : i%2 = 0
  · rcases inputSlots_even a i he with h | h <;>
      simp only [h, Nat.reduceBEq, Bool.false_eq_true, ite_true, ite_false]
  · have ho : i%2 = 1 := by omega
    rw [groupPoint_odd i ho]
    simp only [beq_iff_eq, statusAt_ring_diluted a i hi]

theorem input_leaf (a : Input) (ha : inputCheck a = true) (i : Nat) (hi : i < 8) :
    (inputSpec a i).leaf = (by classical exact decide (i%2 = 1 ∧
      SingleReplacement (inputPattern a) (inputRepresentation a) (ringSites.getD i (0,0)))) := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [inputSpec, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  by_cases he : i%2 = 1
  · have hz : i%2 ≠ 0 := by omega
    have hg := groupPoint_odd i he
    have hc : ringSites.getD i (0,0) ∈ templateCorners := hg ▸ (groupPoint_corner i hi).mpr he
    have ht : ringSites.getD i (0,0) ∉ templateTips := by
      rw [← hg, groupPoint_tip i hi]
      exact hz
    rw [inputSlots_eq a ha i hi, groupSlots_degree _ _ i hi]
    simp only [he, true_and, hg, SingleReplacement, hc, ht,
      and_true, false_or]
    by_cases hd : patternDegree (inputPattern a) (ringSites.getD i (0,0)) = 0
    · simp only [List.getD_eq_getElem?_getD] at hd ⊢
      simp [hd]
    · simp only [List.getD_eq_getElem?_getD] at hd ⊢
      simp [hd, and_comm]
  · simp only [he, false_and]

theorem input_tip (a : Input) (ha : inputCheck a = true) (i : Nat) (hi : i < 8) :
    (inputSpec a i).tip = decide (i%2 = 0 ∧ groupPoint i ∈ reductionGroups (inputPattern a)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [inputSpec, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  by_cases he : i%2 = 0
  · rw [inputSlots_eq a ha i hi, groupSlots_degree _ _ i hi]
    have hm : groupPoint i ∈ reductionGroups (inputPattern a) ↔
        0 < patternDegree (inputPattern a) (groupPoint i) := by
      simp only [reductionGroups, Finset.mem_filter, groupPoint_peripheral i hi, true_and]
    simp only [he, true_and, ite_true, hm]
    by_cases hd : patternDegree (inputPattern a) (groupPoint i) = 0
    · simp only [hd, ite_true]
      norm_num
    · have hp : 0 < patternDegree (inputPattern a) (groupPoint i) := Nat.pos_of_ne_zero hd
      simp only [hd, ite_false, hp, iff_self]
  · simp only [he, false_and]

end AKLT.W.H1C009
