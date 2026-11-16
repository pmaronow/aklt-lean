import AKLT.W.H1C008.Geometry

namespace AKLT.W.H1C008

open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

 theorem compilerSite_mem (i : Nat) (hi : i < 8) :
    compilerSite i ∈ templateCorners ∪ templateTips := by
  interval_cases i <;> norm_num [compilerSite, templateCorners, templateTips]

private theorem compilerSite_tip (i : Nat) (hi : i < 8) :
    compilerSite i ∈ templateTips ↔ i % 2 = 0 := by
  interval_cases i <;> norm_num [compilerSite, templateTips]

private theorem compilerSite_corner (i : Nat) (hi : i < 8) :
    compilerSite i ∈ templateCorners ↔ i % 2 ≠ 0 := by
  interval_cases i <;> norm_num [compilerSite, templateCorners]

 theorem compilerSite_exists (x : Plane) (hx : x ∈ templateCorners ∪ templateTips) :
    ∃ i < 8, compilerSite i = x := by
  simp only [Finset.mem_union, templateCorners, templateTips, Finset.mem_insert,
    Finset.mem_singleton] at hx
  rcases hx with hc | ht
  · rcases hc with rfl | rfl | rfl | rfl
    · exact ⟨1, by omega, by norm_num [compilerSite]⟩
    · exact ⟨3, by omega, by norm_num [compilerSite]⟩
    · exact ⟨5, by omega, by norm_num [compilerSite]⟩
    · exact ⟨7, by omega, by norm_num [compilerSite]⟩
  · rcases ht with rfl | rfl | rfl | rfl
    · exact ⟨0, by omega, by norm_num [compilerSite]⟩
    · exact ⟨2, by omega, by norm_num [compilerSite]⟩
    · exact ⟨4, by omega, by norm_num [compilerSite]⟩
    · exact ⟨6, by omega, by norm_num [compilerSite]⟩

 theorem compilerSite_leader (i : Nat) (hi : i < 8) :
    (groupLeader (compilerSite i)).val = ringLeader i := by
  interval_cases i <;> norm_num [compilerSite, groupLeader, ringLeader]

 theorem compilerSite_second (i : Nat) (hi : i < 8) :
    (groupSecond (compilerSite i)).val = ringLeader i + 1 := by
  have hleader := compilerSite_leader i hi
  have hbound : ringLeader i + 1 ≤ 19 := by
    interval_cases i <;> norm_num [ringLeader]
  simp only [groupSecond, hleader, Nat.min_eq_right hbound]

/-- The compiler counts exactly one token for a single and two for a retained pair. -/
theorem inputSlots_eq (a : Input) (hs : ValidStatuses a) (i : Nat) (hi : i < 8) :
    inputSlots a i =
      if 0 < patternDegree (inputPattern a) (compilerSite i) then
        if groupIsPair (inputPattern a) (inputRepresentation a) (compilerSite i) then 2 else 1
      else 0 := by
  have hd := degree_compilerSite a hs i hi
  have ht := compilerSite_tip i hi
  have hc := compilerSite_corner i hi
  by_cases he : i % 2 = 0
  · cases hb : (rawEdges a.axes a.corners).getD (12+i/2) false <;>
      simp only [List.getD_eq_getElem?_getD] at hb <;>
      simp [inputSlots, groupIsPair, SingleReplacement, hd, ht, hc, he, hb]
  · cases h1 : (rawEdges a.axes a.corners).getD (4+i) false <;>
      cases h2 : (rawEdges a.axes a.corners).getD (4+(i+7)%8) false <;>
      cases hr : a.leafReduced <;>
      simp only [List.getD_eq_getElem?_getD] at h1 h2 <;>
      simp [inputSlots, groupIsPair, SingleReplacement, inputRepresentation,
        hd, ht, hc, he, h1, h2, hr]

 theorem inputSlots_pos (a : Input) (hs : ValidStatuses a) (i : Nat) (hi : i < 8) :
    0 < inputSlots a i ↔ compilerSite i ∈ reductionGroups (inputPattern a) := by
  have hm := compilerSite_mem i hi
  rw [inputSlots_eq a hs i hi]
  simp only [reductionGroups, Finset.mem_filter, hm, true_and]
  split_ifs <;> simp_all

 theorem inputSlots_two (a : Input) (hs : ValidStatuses a) (i : Nat) (hi : i < 8) :
    inputSlots a i = 2 ↔ compilerSite i ∈ reductionGroups (inputPattern a) ∧
      groupIsPair (inputPattern a) (inputRepresentation a) (compilerSite i) = true := by
  have hm := compilerSite_mem i hi
  rw [inputSlots_eq a hs i hi]
  simp only [reductionGroups, Finset.mem_filter, hm, true_and]
  split_ifs <;> simp_all

 theorem inputSlots_le_two (a : Input) (hs : ValidStatuses a) (i : Nat) (hi : i < 8) :
    inputSlots a i ≤ 2 := by
  rw [inputSlots_eq a hs i hi]
  split_ifs <;> omega

#print axioms compilerSite_mem
#print axioms compilerSite_exists
#print axioms compilerSite_leader
#print axioms compilerSite_second
#print axioms inputSlots_eq
#print axioms inputSlots_pos
#print axioms inputSlots_two
#print axioms inputSlots_le_two

end AKLT.W.H1C008
