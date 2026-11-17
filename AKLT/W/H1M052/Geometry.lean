module
public import AKLT.W.H1M052.Pauli

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs AKLT.Blueprint.H1

namespace AKLT.W.H1M052

def groupTokens (π : PatternData) (r : Representation) (x : Plane) : Finset (Fin 20) :=
  if groupIsPair π r x then {groupLeader x, groupSecond x} else {groupLeader x}

theorem group_mem_boundary (π : PatternData) (x : reductionGroups π) :
    x.val ∈ templateCorners ∪ templateTips := (Finset.mem_filter.mp x.property).1

theorem leader_owner (x : Plane) (hx : x ∈ templateCorners ∪ templateTips) :
    (externalSlot (groupLeader x)).1 = x := by
  simp only [templateCorners, templateTips, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton] at hx
  rcases hx with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl) <;> decide +kernel

theorem second_owner (x : Plane) (hx : x ∈ templateCorners) :
    (externalSlot (groupSecond x)).1 = x := by
  simp only [templateCorners, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel

theorem pair_corner (π : PatternData) (r : Representation) (x : Plane)
    (h : groupIsPair π r x = true) :
    x ∈ templateCorners ∧ ¬ SingleReplacement π r x := by
  simpa only [groupIsPair, decide_eq_true_eq] using h

theorem token_owner (π : PatternData) (r : Representation) (x : Plane)
    (hx : x ∈ reductionGroups π) (j : Fin 20) (hj : j ∈ groupTokens π r x) :
    (externalSlot j).1 = x := by
  have hb := (Finset.mem_filter.mp hx).1
  unfold groupTokens at hj
  split_ifs at hj with hp
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · exact leader_owner x hb
    · exact second_owner x (pair_corner π r x hp).1
  · simp only [Finset.mem_singleton] at hj
    subst j
    exact leader_owner x hb

theorem groupTokens_disjoint (π : PatternData) (r : Representation) :
    (reductionGroups π : Set Plane).PairwiseDisjoint (groupTokens π r) := by
  intro x hx y hy hxy
  apply Finset.disjoint_left.mpr
  intro j hjx hjy
  exact hxy ((token_owner π r x hx j hjx).symm.trans (token_owner π r y hy j hjy))

theorem group_pair_distinct (x : Plane) : groupLeader x ≠ groupSecond x := by
  have hBound : (groupLeader x).val < 19 := by
    unfold groupLeader
    split_ifs <;> norm_num
  intro h
  have hv := congrArg Fin.val h
  change (groupLeader x).val = min 19 ((groupLeader x).val + 1) at hv
  omega

theorem pair_ne_origin (π : PatternData) (r : Representation) (x : Plane)
    (h : groupIsPair π r x = true) : x ≠ (0, 0) := by
  have hc := (pair_corner π r x h).1
  simp only [templateCorners, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> decide +kernel

theorem pair_retained (π : PatternData) (r : Representation) (x : reductionGroups π)
    (h : groupIsPair π r x.val = true) : x.val ∈ reducedSpinSites π r := by
  obtain ⟨hc, hs⟩ := pair_corner π r x.val h
  have hd := (Finset.mem_filter.mp x.property).2
  obtain ⟨e, he⟩ := Finset.card_pos.mp hd
  have he' := Finset.mem_filter.mp he
  have hb := Finset.mem_filter.mp he'.1
  have hstatus : π.statusAt x.val ≠ .X := by
    rcases he'.2 with hx | hx
    · simpa [← hx] using hb.2.1
    · simpa [← hx] using hb.2.2.1
  have hxsite : x.val ∈ templateSites := by
    simp only [templateCorners, Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with hx | hx | hx | hx <;> rw [hx] <;> decide +kernel
  have htip : x.val ∉ templateTips := by
    simp only [templateCorners, Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with hx | hx | hx | hx <;> rw [hx] <;> decide +kernel
  simp only [reducedSpinSites, Finset.mem_filter, PatternData.active]
  exact ⟨⟨hxsite, hstatus⟩, htip, Or.inr ⟨by omega, hs⟩⟩

def groupVector (π : PatternData) (r : Representation) (n : Plane → Vec3)
    (x : Plane) : Vec3 :=
  if groupIsPair π r x then n x else (replacementRadius π x : ℝ) • n (leafNeighbor π x)

def tokenVector (π : PatternData) (r : Representation) (n : Plane → Vec3)
    (j : Fin 20) : Vec3 := groupVector π r n (externalSlot j).1

theorem tokenVector_at_group (π : PatternData) (r : Representation) (n : Plane → Vec3)
    (x : Plane) (hx : x ∈ reductionGroups π) (j : Fin 20)
    (hj : j ∈ groupTokens π r x) : tokenVector π r n j = groupVector π r n x := by
  simp only [tokenVector, token_owner π r x hx j hj]

theorem tokenVector_leader (π : PatternData) (r : Representation) (n : Plane → Vec3)
    (x : reductionGroups π) (h : groupIsPair π r x.val = true) :
    tokenVector π r n (groupLeader x.val) = n x.val := by
  simp [tokenVector, leader_owner x.val (group_mem_boundary π x), groupVector, h]

theorem tokenVector_second (π : PatternData) (r : Representation) (n : Plane → Vec3)
    (x : reductionGroups π) (h : groupIsPair π r x.val = true) :
    tokenVector π r n (groupSecond x.val) = n x.val := by
  simp [tokenVector, second_owner x.val (pair_corner π r x.val h).1, groupVector, h]

end AKLT.W.H1M052
