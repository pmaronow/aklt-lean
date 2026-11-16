import AKLT.Cert.H1.Production.Leaves

namespace AKLT.W.H1C008

open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

/-- Every raw status used in a compiler input is one of the three status digits. -/
def ValidStatuses (a : Input) : Prop :=
  (∀ i, (a.axes.getD i ⟨0,0⟩).status ≤ 2) ∧
  (∀ i, (a.corners.getD i ⟨0,0⟩).status ≤ 2)

private instance : LawfulBEq RawOption where
  rfl := by
    intro a
    cases a with
    | mk s m =>
      change (s == s && m == m) = true
      simp only [beq_self_eq_true, Bool.and_self]
  eq_of_beq := by
    intro a b h
    cases a with
    | mk sa ma =>
      cases b with
      | mk sb mb =>
        change (sa == sb && ma == mb) = true at h
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        rcases h with ⟨rfl,rfl⟩
        rfl

private theorem inputCheck_fields (a : Input) (h : inputCheck a = true) :
    (a.axes.zipIdx).all (fun (x,i) => (axialOptions i).contains x) = true ∧
    (a.corners.zipIdx).all (fun (x,i) => cornerOptions.contains x &&
      cornerCompatible a.axes i x) = true ∧
    a.inversion.all (fun i => (inputTokens a).contains i) = true ∧
    (List.range 8).all (fun i => inputSlots a i != 2 ||
      (a.inversion.contains (ringLeader i) == a.inversion.contains (ringLeader i+1))) = true := by
  simp only [inputCheck, Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨_,_⟩,_⟩,haxes⟩,hcorners⟩,_⟩,_⟩,hinv⟩,hpairs⟩
  exact ⟨haxes,hcorners,hinv,hpairs⟩

private theorem axial_status (i : Nat) (o : RawOption) (ho : o ∈ axialOptions i) :
    o.status ≤ 2 := by
  by_cases h3 : i = 3
  · simp [axialOptions, h3] at ho
    rcases ho with rfl | rfl | rfl | rfl <;> norm_num
  · simp [axialOptions, h3] at ho
    rcases ho with rfl | rfl | ⟨d,_,rfl⟩ <;> norm_num

private theorem corner_status (o : RawOption) (ho : o ∈ cornerOptions) :
    o.status ≤ 2 := by
  simp only [cornerOptions, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

 theorem validStatuses_of_check (a : Input) (h : inputCheck a = true) :
    ValidStatuses a := by
  obtain ⟨haxes,hcorners,_,_⟩ := inputCheck_fields a h
  have ha := List.forall_mem_zipIdx'.mp (List.all_eq_true.mp haxes)
  have hc := List.forall_mem_zipIdx'.mp (List.all_eq_true.mp hcorners)
  constructor
  · intro i
    by_cases hi : i < a.axes.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact axial_status i _ (List.contains_iff_mem.mp (ha i hi))
    · rw [List.getD_eq_default _ _ (by omega)]
      norm_num
  · intro i
    by_cases hi : i < a.corners.length
    · rw [List.getD_eq_getElem _ _ hi]
      have hiCheck := hc i hi
      simp only [Bool.and_eq_true] at hiCheck
      exact corner_status _ (List.contains_iff_mem.mp hiCheck.1)
    · rw [List.getD_eq_default _ _ (by omega)]
      norm_num

 theorem inputInversion_mem (a : Input) (j : Fin 20) :
    j ∈ inputInversion a ↔ a.inversion.contains j.val = true := by
  classical
  simp [inputInversion, List.mem_filterMap, Fin.ext_iff]

 theorem inputTokens_mem (a : Input) (n : Nat) :
    n ∈ inputTokens a ↔ ∃ i < 8, ∃ k < inputSlots a i, n = ringLeader i + k := by
  simp [inputTokens, List.mem_flatMap, List.mem_range, List.mem_map, eq_comm]

 theorem inversion_supported (a : Input) (h : inputCheck a = true) :
    ∀ n ∈ a.inversion, n ∈ inputTokens a := by
  intro n hn
  exact List.contains_iff_mem.mp (List.all_eq_true.mp (inputCheck_fields a h).2.2.1 n hn)

 theorem inversion_pairs (a : Input) (h : inputCheck a = true) (i : Nat) (hi : i < 8)
    (hslots : inputSlots a i = 2) :
    a.inversion.contains (ringLeader i) = a.inversion.contains (ringLeader i+1) := by
  have hp := List.all_eq_true.mp (inputCheck_fields a h).2.2.2 i (List.mem_range.mpr hi)
  simpa [hslots] using hp

#print axioms validStatuses_of_check
#print axioms inputInversion_mem
#print axioms inputTokens_mem
#print axioms inversion_supported
#print axioms inversion_pairs

end AKLT.W.H1C008
