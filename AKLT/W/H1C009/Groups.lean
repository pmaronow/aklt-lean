import AKLT.W.H1C009.Edges
import AKLT.W.H1C009.Degrees

namespace AKLT.W.H1C009
open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

theorem groupPoint_corner (i : Nat) (hi : i < 8) :
    groupPoint i ∈ templateCorners ↔ i%2 = 1 := by
  interval_cases i <;> simp [groupPoint, ringSites, templateCorners]

theorem groupPoint_tip (i : Nat) (hi : i < 8) :
    groupPoint i ∈ templateTips ↔ i%2 = 0 := by
  interval_cases i <;> simp [groupPoint, ringSites, templateTips]

theorem groupPoint_peripheral (i : Nat) (hi : i < 8) :
    groupPoint i ∈ templateCorners ∪ templateTips := by
  rw [Finset.mem_union, groupPoint_corner i hi, groupPoint_tip i hi]
  omega

theorem groupPoint_odd (i : Nat) (h : i%2 = 1) :
    groupPoint i = ringSites.getD i (0,0) := by
  simp only [groupPoint, h, Nat.reduceBEq, Bool.false_eq_true, ite_false]

theorem groupLeader_index (i : Nat) (hi : i < 8) :
    (groupLeader (groupPoint i)).val = ringLeader i := by
  interval_cases i <;> simp [groupLeader, groupPoint, ringSites, ringLeader]

theorem inputInversion_mem (a : Input) (j : Fin 20) :
    j ∈ inputInversion a ↔ j.val ∈ a.inversion := by
  simp only [inputInversion, List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨k,hk,h⟩
    split_ifs at h with hlt
    · have he := congrArg Fin.val (Option.some.inj h)
      simpa only [← he] using hk
  · intro h
    refine ⟨j.val,h,?_⟩
    have he : (⟨j.val,j.isLt⟩ : Fin 20) = j := Fin.ext rfl
    exact (dite_eq_left j.isLt).trans (congrArg some he)

theorem input_inverted (a : Input) (i : Nat) (hi : i < 8) :
    a.inversion.contains (ringLeader i) = decide (groupLeader (groupPoint i) ∈ inputInversion a) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem, decide_eq_true_eq, inputInversion_mem,
    groupLeader_index i hi]

/-- Tip degrees are measured at the tip endpoint; corner degrees use both ring edges. -/
theorem input_degree (a : Input) (ha : inputCheck a = true) (i : Nat) (hi : i < 8) :
    patternDegree (inputPattern a) (groupPoint i) =
      groupDegreeBits (fun j => (rawEdges a.axes a.corners).getD j false) i := by
  rw [degree_group _ i hi]
  unfold groupDegreeBits
  dsimp only
  split_ifs
  · rw [oriented_edge _ (12+i/2) (by omega), raw_edge a ha _ (by omega)]
  · rw [oriented_edge _ (4+i) (by omega), raw_edge a ha _ (by omega),
      oriented_edge _ (4+(i+7)%8) (by omega), raw_edge a ha _ (by omega)]

theorem groupSlots_degree (π : PatternData) (r : Representation) (i : Nat) (hi : i < 8) :
    groupSlots π r (groupPoint i) =
      if patternDegree π (groupPoint i) = 0 then 0
      else if i%2 = 0 then 1
      else if r = .reduced ∧ patternDegree π (groupPoint i) = 1 then 1 else 2 := by
  have hmem : groupPoint i ∈ reductionGroups π ↔ 0 < patternDegree π (groupPoint i) := by
    simp only [reductionGroups, Finset.mem_filter, groupPoint_peripheral i hi, true_and]
  have hc := groupPoint_corner i hi
  have ht := groupPoint_tip i hi
  unfold groupSlots
  simp only [hmem, groupIsPair, SingleReplacement, hc, ht]
  by_cases hd : patternDegree π (groupPoint i) = 0
  · simp [hd]
  · have hp : 0 < patternDegree π (groupPoint i) := by omega
    by_cases he : i%2 = 0
    · simp [hd,hp,he]
    · have ho : i%2 = 1 := by omega
      by_cases hr : r = .reduced <;>
        by_cases h1 : patternDegree π (groupPoint i) = 1 <;> simp [hd,hp,ho,hr,h1]

theorem inputSlots_eq (a : Input) (ha : inputCheck a = true) (i : Nat) (hi : i < 8) :
    inputSlots a i = groupSlots (inputPattern a) (inputRepresentation a) (groupPoint i) := by
  rw [groupSlots_degree _ _ i hi, input_degree a ha i hi]
  unfold inputSlots groupDegreeBits inputRepresentation
  by_cases he : i%2 = 0
  · simp only [he, beq_self_eq_true, ite_true]
    cases hb : (rawEdges a.axes a.corners).getD (12+i/2) false <;> simp
  · simp only [show (i%2 == 0) = false by simp [he], ite_false, he]
    cases hr : a.leafReduced <;> simp

end AKLT.W.H1C009
