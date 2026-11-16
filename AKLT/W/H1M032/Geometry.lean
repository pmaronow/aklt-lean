import AKLT.Blueprint.H1.NodesSector

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.H1M032

/-- All sixteen potential group slots have distinct encodings. -/
theorem raw_slot_injective :
    ∀ x y : ↥(templateCorners ∪ templateTips), ∀ a b : Fin 2,
      (if a = 0 then groupLeader x.val else groupSecond x.val) =
        (if b = 0 then groupLeader y.val else groupSecond y.val) → x = y ∧ a = b := by
  decide +kernel

def boundaryGroup (π : PatternData) (x : reductionGroups π) :
    ↥(templateCorners ∪ templateTips) :=
  ⟨x.val, (Finset.mem_filter.mp x.property).1⟩

theorem leader_second_ne (π : PatternData) (x : reductionGroups π) :
    groupLeader x.val ≠ groupSecond x.val := by
  intro h
  have h' := (raw_slot_injective (boundaryGroup π x) (boundaryGroup π x) 0 1 h).2
  exact (by decide : (0 : Fin 2) ≠ 1) h'

theorem different_group_slots (π : PatternData) (x y : reductionGroups π) (hxy : x ≠ y) :
    groupLeader x.val ≠ groupLeader y.val ∧
    groupLeader x.val ≠ groupSecond y.val ∧
    groupSecond x.val ≠ groupLeader y.val ∧
    groupSecond x.val ≠ groupSecond y.val := by
  have h (a b : Fin 2) :
      (if a = 0 then groupLeader x.val else groupSecond x.val) ≠
        (if b = 0 then groupLeader y.val else groupSecond y.val) := by
    intro heq
    have h' := (raw_slot_injective (boundaryGroup π x) (boundaryGroup π y) a b heq).1
    have hv := congrArg (fun z : ↥(templateCorners ∪ templateTips) => z.val) h'
    exact hxy (Subtype.ext hv)
  exact ⟨h 0 0, h 0 1, h 1 0, h 1 1⟩

/-- A harmless totalization used only to write uniform two-coordinate formulas. -/
def secondOrLeader (π : PatternData) (r : Representation) (x : reductionGroups π) :
    reductionVectors π r :=
  if h : groupIsPair π r x.val = true then secondToken π r x h else leaderToken π r x

def groupSlots (π : PatternData) (r : Representation) (x : reductionGroups π) :
    Finset (reductionVectors π r) :=
  if groupIsPair π r x.val then {leaderToken π r x, secondOrLeader π r x}
    else {leaderToken π r x}

theorem pair_tokens_ne (π : PatternData) (r : Representation) (x : reductionGroups π)
    (h : groupIsPair π r x.val = true) :
    leaderToken π r x ≠ secondOrLeader π r x := by
  intro heq
  apply leader_second_ne π x
  simpa [secondOrLeader, h, leaderToken, secondToken] using congrArg Subtype.val heq

theorem groupSlots_cover (π : PatternData) (r : Representation) :
    Finset.univ.biUnion (groupSlots π r) = Finset.univ := by
  classical
  apply Finset.ext
  intro j
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, iff_true]
  rcases Finset.mem_biUnion.mp j.property with ⟨x, hx, hj⟩
  refine ⟨⟨x, hx⟩, ?_⟩
  by_cases hp : groupIsPair π r x = true
  · simp only [hp, ↓reduceIte, Finset.mem_insert, Finset.mem_singleton] at hj
    simp only [groupSlots, hp, ↓reduceIte, Finset.mem_insert, Finset.mem_singleton]
    rcases hj with hj | hj
    · exact Or.inl (Subtype.ext hj)
    · exact Or.inr (Subtype.ext (by simpa [secondOrLeader, hp, secondToken] using hj))
  · have hp' : groupIsPair π r x = false := Bool.eq_false_iff.mpr hp
    simp only [hp', Bool.false_eq_true, ↓reduceIte, Finset.mem_singleton] at hj
    simp only [groupSlots, hp', Bool.false_eq_true, ↓reduceIte, Finset.mem_singleton]
    exact Subtype.ext hj

theorem mem_groupSlots_val (π : PatternData) (r : Representation)
    (x : reductionGroups π) (j : reductionVectors π r) (hj : j ∈ groupSlots π r x) :
    j.val = groupLeader x.val ∨ j.val = groupSecond x.val := by
  classical
  by_cases hp : groupIsPair π r x.val = true
  · simp only [groupSlots, hp, ↓reduceIte, Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with hj | hj
    · exact Or.inl (congrArg Subtype.val hj)
    · apply Or.inr
      simpa only [secondOrLeader, hp, ↓reduceDIte, secondToken] using congrArg Subtype.val hj
  · simp only [groupSlots, hp, Bool.false_eq_true, ↓reduceIte, Finset.mem_singleton] at hj
    exact Or.inl (congrArg Subtype.val hj)

theorem groupSlots_disjoint (π : PatternData) (r : Representation) :
    Set.PairwiseDisjoint (↑(Finset.univ : Finset (reductionGroups π))) (groupSlots π r) := by
  classical
  intro x _ y _ hxy
  apply Finset.disjoint_left.mpr
  intro j hx hy
  have hsep := different_group_slots π x y hxy
  have hxv := mem_groupSlots_val π r x j hx
  have hyv := mem_groupSlots_val π r y j hy
  rcases hxv with hxv | hxv <;> rcases hyv with hyv | hyv
  all_goals
    have heq := hxv.symm.trans hyv
    tauto

theorem leader_mem_groupSlots (π : PatternData) (r : Representation) (x : reductionGroups π) :
    leaderToken π r x ∈ groupSlots π r x := by
  classical
  by_cases hp : groupIsPair π r x.val = true <;> simp [groupSlots, hp]

theorem second_mem_groupSlots (π : PatternData) (r : Representation) (x : reductionGroups π) :
    secondOrLeader π r x ∈ groupSlots π r x := by
  classical
  by_cases hp : groupIsPair π r x.val = true
  · simp only [groupSlots, hp, ↓reduceIte, Finset.mem_insert, Finset.mem_singleton,
      or_true]
  · simp only [groupSlots, secondOrLeader, hp, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte,
      Finset.mem_singleton]

theorem other_group_tokens_ne (π : PatternData) (r : Representation)
    (x y : reductionGroups π) (hyx : y ≠ x)
    (j : reductionVectors π r) (hj : j ∈ groupSlots π r x) :
    leaderToken π r y ≠ j ∧ secondOrLeader π r y ≠ j := by
  classical
  have hd := groupSlots_disjoint π r (Finset.mem_univ x) (Finset.mem_univ y) hyx.symm
  have hn : j ∉ groupSlots π r y := Finset.disjoint_left.mp hd hj
  constructor
  · intro h
    exact hn (h ▸ leader_mem_groupSlots π r y)
  · intro h
    exact hn (h ▸ second_mem_groupSlots π r y)

end AKLT.W.H1M032
