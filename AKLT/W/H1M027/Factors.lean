module
public import AKLT.Blueprint.H1.NodesReduction

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs AKLT.Blueprint.H1

namespace AKLT.W.H1M027

theorem dot_symm (a b : Vec3) : dot a b = dot b a := by
  simp only [dot, mul_comm]

theorem normSq_zero : normSq (0 : Vec3) = 0 := by
  simp [normSq, dot]

theorem supportSpins_ball (hIco : ∀ j : IcoLetter, normSq (icoVector j) = 1)
    (V : Finset Plane) (n : V → SpinLetter) (x : Plane) :
    normSq (supportSpins V n x) ≤ 1 := by
  classical
  unfold supportSpins
  split
  · cases n _ with
    | none => simp [spinVector, normSq_zero]
    | some j => simp [spinVector, hIco]
  · simp [normSq_zero]

theorem corner_not_tip {x : Plane} (hx : x ∈ templateCorners) : x ∉ templateTips := by
  simp only [templateCorners, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> decide

theorem slot_peripheral (j : Fin 20) :
    (externalSlot j).1 ∈ templateCorners ∪ templateTips := by
  fin_cases j <;> decide

theorem leader_site {x : Plane} (hx : x ∈ templateCorners ∪ templateTips) :
    (externalSlot (groupLeader x)).1 = x := by
  simp only [Finset.mem_union, templateCorners, templateTips,
    Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl) <;> decide

theorem second_site {x : Plane} (hx : x ∈ templateCorners) :
    (externalSlot (groupSecond x)).1 = x := by
  simp only [templateCorners, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> decide

theorem corner_field (m : Fin 20 → UnitVector) {x : Plane}
    (hx : x ∈ templateCorners) (z : Vec3) :
    coveredSiteField m x z =
      (1 + dot (m (groupLeader x)).val z) *
      (1 + dot (m (groupSecond x)).val z) := by
  simp only [templateCorners, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
    simp [coveredSiteField, Fin.prod_univ_succ, externalSlot, groupLeader, groupSecond]

theorem degree_pos_active (π : PatternData) {x : Plane}
    (hx : 0 < patternDegree π x) : x ∈ π.active := by
  classical
  obtain ⟨e, he⟩ := Finset.card_pos.mp hx
  obtain ⟨hb, he⟩ := Finset.mem_filter.mp he
  have hb' := Finset.mem_filter.mp hb
  obtain ⟨a, ha, h⟩ := Finset.mem_biUnion.mp hb'.1
  obtain ⟨b, hbmem, hab⟩ := Finset.mem_image.mp h
  have hends : e.1 ∈ templateSites ∧ e.2 ∈ templateSites := by
    subst e
    exact ⟨ha, (Finset.mem_inter.mp hbmem).2⟩
  apply Finset.mem_filter.mpr
  rcases he with he | he
  · exact ⟨he ▸ hends.1, he ▸ hb'.2.1⟩
  · exact ⟨he ▸ hends.2, he ▸ hb'.2.2.1⟩

theorem retained_peripheral_iff (π : PatternData) (r : Representation) {x : Plane}
    (hx : x ∈ templateCorners ∪ templateTips) :
    x ∈ reducedSpinSites π r ↔
      0 < patternDegree π x ∧ groupIsPair π r x = true := by
  classical
  constructor
  · intro hv
    obtain ⟨ha, ht, hc⟩ := Finset.mem_filter.mp hv
    have hcorner : x ∈ templateCorners := (Finset.mem_union.mp hx).resolve_right ht
    obtain ⟨hd, hs⟩ := hc.resolve_left (not_not_intro hcorner)
    exact ⟨Nat.pos_of_ne_zero hd, by simp [groupIsPair, hcorner, hs]⟩
  · rintro ⟨hd, hp⟩
    have hp' : x ∈ templateCorners ∧ ¬ SingleReplacement π r x := by
      simpa [groupIsPair] using hp
    exact Finset.mem_filter.mpr ⟨degree_pos_active π hd,
      corner_not_tip hp'.1, Or.inr ⟨Nat.ne_of_gt hd, hp'.2⟩⟩

/-- Put a deleted site's chosen vector in its leader slot. Retained corner
slots keep their original vectors; all slots outside the reduced support are zero. -/
def assignedVectors (π : PatternData) (r : Representation) (m : Fin 20 → UnitVector)
    (v : {x // x ∈ deletedLeafSites π r} → Vec3) (j : Fin 20) : Vec3 :=
  if j ∈ reductionVectors π r then
    if h : (externalSlot j).1 ∈ deletedLeafSites π r then v ⟨_, h⟩ else (m j).val
  else 0

theorem assignedVectors_ball (π : PatternData) (r : Representation)
    (m : Fin 20 → UnitVector) (v : {x // x ∈ deletedLeafSites π r} → Vec3)
    (hv : ∀ x, normSq (v x) ≤ 1) (j : Fin 20) :
    normSq (assignedVectors π r m v j) ≤ 1 := by
  classical
  unfold assignedVectors
  split
  · split
    · exact hv _
    · exact le_of_eq (m j).property
  · simp [normSq_zero]

theorem retained_field_product (π : PatternData) (r : Representation)
    (m : Fin 20 → UnitVector) (n : Plane → Vec3) :
    (∏ j : Fin 20, if (externalSlot j).1 ∈ reducedSpinSites π r then
      1 + dot (m j).val (n (externalSlot j).1) else 1) =
    ∏ x ∈ templateCorners ∪ templateTips,
      if x ∈ reducedSpinSites π r then coveredSiteField m x (n x) else 1 := by
  classical
  symm
  calc
    _ = ∏ x ∈ templateCorners ∪ templateTips, ∏ j : Fin 20,
        if (externalSlot j).1 = x then
          (if x ∈ reducedSpinSites π r then 1 + dot (m j).val (n x) else 1)
        else 1 := by
      apply Finset.prod_congr rfl
      intro x hx
      by_cases hv : x ∈ reducedSpinSites π r <;> simp [coveredSiteField, hv]
    _ = ∏ j : Fin 20, ∏ x ∈ templateCorners ∪ templateTips,
        if (externalSlot j).1 = x then
          (if x ∈ reducedSpinSites π r then 1 + dot (m j).val (n x) else 1)
        else 1 := Finset.prod_comm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [Finset.prod_ite_eq, ite_eq_left (slot_peripheral j)]

def leafRemainder (π : PatternData) (r : Representation)
    (v : {x // x ∈ deletedLeafSites π r} → Vec3) (n : Plane → Vec3) (x : Plane) : ℝ :=
  if h : x ∈ deletedLeafSites π r then
    if patternDegree π x = 0 then 1 else
      1 + (replacementRadius π x : ℝ) * dot (v ⟨x, h⟩) (n (leafNeighbor π x))
  else 1

def groupFactor (π : PatternData) (r : Representation) (u : Fin 20 → Vec3)
    (n : Plane → Vec3) (x : Plane) : ℝ :=
  if groupIsPair π r x then
    (1 + dot (n x) (u (groupLeader x))) * (1 + dot (n x) (u (groupSecond x)))
  else 1 + (replacementRadius π x : ℝ) * dot (n (leafNeighbor π x)) (u (groupLeader x))

theorem assigned_leader (π : PatternData) (r : Representation) (m : Fin 20 → UnitVector)
    (v : {x // x ∈ deletedLeafSites π r} → Vec3) {x : Plane}
    (hx : x ∈ reductionGroups π) :
    assignedVectors π r m v (groupLeader x) =
      if h : x ∈ deletedLeafSites π r then v ⟨x, h⟩ else (m (groupLeader x)).val := by
  classical
  have ht : groupLeader x ∈ reductionVectors π r := by
    apply Finset.mem_biUnion.mpr
    refine ⟨x, hx, ?_⟩
    split <;> simp
  simp only [assignedVectors, ite_eq_left ht, leader_site (Finset.mem_filter.mp hx).1]

theorem assigned_second (π : PatternData) (r : Representation) (m : Fin 20 → UnitVector)
    (v : {x // x ∈ deletedLeafSites π r} → Vec3) {x : Plane}
    (hx : x ∈ reductionGroups π) (hp : groupIsPair π r x = true) :
    assignedVectors π r m v (groupSecond x) = (m (groupSecond x)).val := by
  classical
  have hc : x ∈ templateCorners := (of_decide_eq_true hp).1
  have hv : x ∈ reducedSpinSites π r :=
    (retained_peripheral_iff π r (Finset.mem_filter.mp hx).1).mpr
      ⟨(Finset.mem_filter.mp hx).2, hp⟩
  have hd : x ∉ deletedLeafSites π r := by simp [deletedLeafSites, hv]
  have ht : groupSecond x ∈ reductionVectors π r := by
    apply Finset.mem_biUnion.mpr
    exact ⟨x, hx, by simp [hp]⟩
  simp [assignedVectors, ht, second_site hc, hd]

theorem peripheral_factor (π : PatternData) (r : Representation)
    (m : Fin 20 → UnitVector) (v : {x // x ∈ deletedLeafSites π r} → Vec3)
    (n : Plane → Vec3) {x : Plane} (hx : x ∈ templateCorners ∪ templateTips) :
    (if x ∈ reducedSpinSites π r then coveredSiteField m x (n x) else 1) *
        leafRemainder π r v n x =
      if 0 < patternDegree π x then groupFactor π r (assignedVectors π r m v) n x else 1 := by
  classical
  by_cases hpos : 0 < patternDegree π x
  · have hg : x ∈ reductionGroups π := Finset.mem_filter.mpr ⟨hx, hpos⟩
    by_cases hp : groupIsPair π r x = true
    · have hv := (retained_peripheral_iff π r hx).mpr ⟨hpos, hp⟩
      have hd : x ∉ deletedLeafSites π r := by simp [deletedLeafSites, hv]
      have hc : x ∈ templateCorners := (of_decide_eq_true hp).1
      simp [hpos, hv, leafRemainder, hd, groupFactor, hp,
        assigned_leader π r m v hg, assigned_second π r m v hg hp,
        corner_field m hc, dot_symm]
    · have hv : x ∉ reducedSpinSites π r := by
        rw [retained_peripheral_iff π r hx]
        simp [hp]
      have hd : x ∈ deletedLeafSites π r :=
        Finset.mem_sdiff.mpr ⟨degree_pos_active π hpos, hv⟩
      simp [hpos, hv, leafRemainder, hd, groupFactor, hp,
        assigned_leader π r m v hg, Nat.ne_of_gt hpos, dot_symm]
  · have hz : patternDegree π x = 0 := by omega
    have hv : x ∉ reducedSpinSites π r := by
      rw [retained_peripheral_iff π r hx]
      simp [hz]
    simp [hv, leafRemainder, hz]

theorem evaluate_reducedIntegrand (π : PatternData) (r : Representation)
    (next : Bool) (n : Plane → Vec3) (u : Fin 20 → Vec3) :
    localEvaluation (reducedIntegrand π r next) n u =
      (∏ e ∈ π.bonds, if e.1 ∈ reducedSpinSites π r ∧ e.2 ∈ reducedSpinSites π r ∧
        ¬ (next ∧ ({e.1, e.2} : Finset Plane) = {(0, 0), π.outgoing.step}) then
          1 + dot (n e.1) (n e.2) else 1) *
      ∏ x ∈ reductionGroups π, groupFactor π r u n x := by
  classical
  simp [localEvaluation, reducedIntegrand, formalDot, dot, groupFactor, apply_ite]

end AKLT.W.H1M027
