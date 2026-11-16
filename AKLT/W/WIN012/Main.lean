import AKLT.Blueprint.Win.NodesTopology

noncomputable section
open AKLT.Defs

namespace AKLT.W.WIN012

open AKLT.Blueprint.Win

private theorem natAbs_sub_le_one_iff (a b : ℤ) :
    (a - b).natAbs ≤ 1 ↔ b - 1 ≤ a ∧ a ≤ b + 1 := by
  have hsq : (a - b).natAbs ≤ (1 : ℤ).natAbs ↔
      (a - b) ^ 2 ≤ (1 : ℤ) ^ 2 := Int.natAbs_le_iff_sq_le
  norm_num at hsq
  exact hsq.trans (by
    constructor
    · intro h
      have hab := abs_le.mp h
      constructor <;> omega
    · intro h
      exact abs_le.mpr ⟨by omega, by omega⟩)

private theorem mem_starBall_iff (x y : Plane) :
    x ∈ starBall y ↔ supDist x y ≤ 1 := by
  unfold starBall supDist
  simp only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc, max_le_iff]
  rw [natAbs_sub_le_one_iff, natAbs_sub_le_one_iff]

private theorem supDist_eq_zero_iff (x y : Plane) :
    supDist x y = 0 ↔ x = y := by
  change max (x.1 - y.1).natAbs (x.2 - y.2).natAbs = 0 ↔ x = y
  constructor
  · intro h
    have h₁ : (x.1 - y.1).natAbs = 0 := by omega
    have h₂ : (x.2 - y.2).natAbs = 0 := by omega
    simp only [Int.natAbs_eq_zero] at h₁ h₂
    exact Prod.ext (sub_eq_zero.mp h₁) (sub_eq_zero.mp h₂)
  · intro h
    cases h
    simp

private theorem setDistance_eq_one_iff (U : Finset Plane) (z : Plane) :
    setDistance supDist z (↑U : Set Plane) = 1 ↔
      z ∉ U ∧ ∃ y ∈ U, supDist z y = 1 := by
  classical
  constructor
  · intro hdist
    have hnot : z ∉ U := by
      intro hz
      have hle : setDistance supDist z (↑U : Set Plane) ≤ 0 := by
        unfold setDistance
        let y : (↑U : Set Plane) := ⟨z, hz⟩
        calc
          (⨅ w : (↑U : Set Plane), (supDist z w.val : ℕ∞)) ≤
              (supDist z y.val : ℕ∞) := iInf_le _ y
          _ = 0 := by simp [supDist_eq_zero_iff, y]
      rw [hdist] at hle
      norm_num at hle
    have hex : ∃ y : (↑U : Set Plane), supDist z y.val ≤ 1 := by
      by_contra hn
      have htwo : (2 : ℕ∞) ≤ setDistance supDist z (↑U : Set Plane) := by
        unfold setDistance
        apply le_iInf
        intro y
        have hnotle : ¬ supDist z y.val ≤ 1 := by
          intro hy
          exact hn ⟨y, hy⟩
        have hnat : 2 ≤ supDist z y.val := by omega
        exact_mod_cast hnat
      rw [hdist] at htwo
      norm_num at htwo
    obtain ⟨y, hy⟩ := hex
    have hne : z ≠ y.val := by
      intro heq
      exact hnot (heq ▸ y.property)
    have hpos : 0 < supDist z y.val := Nat.pos_of_ne_zero (by
      intro hzero
      exact hne ((supDist_eq_zero_iff z y.val).mp hzero))
    have heq : supDist z y.val = 1 := by omega
    exact ⟨hnot, y.val, y.property, heq⟩
  · rintro ⟨hnot, y, hy, hdist⟩
    apply le_antisymm
    · unfold setDistance
      let w : (↑U : Set Plane) := ⟨y, hy⟩
      calc
        (⨅ t : (↑U : Set Plane), (supDist z t.val : ℕ∞)) ≤
            (supDist z w.val : ℕ∞) := iInf_le _ w
        _ = 1 := by
          change (supDist z y : ℕ∞) = 1
          exact_mod_cast hdist
    · unfold setDistance
      apply le_iInf
      intro w
      have hne : z ≠ w.val := by
        intro heq
        exact hnot (heq ▸ w.property)
      have hpos : 1 ≤ supDist z w.val := Nat.one_le_iff_ne_zero.mpr (by
        intro hzero
        exact hne ((supDist_eq_zero_iff z w.val).mp hzero))
      exact_mod_cast hpos

theorem main : AKLT.Blueprint.Win.BoundaryMembershipStatement := by
  classical
  intro U z
  rw [rawBoundary, Finset.mem_sdiff, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨y, hy, hzball⟩, hnot⟩
    have hdistle : supDist z y ≤ 1 := (mem_starBall_iff z y).mp hzball
    have hne : z ≠ y := by
      intro heq
      subst z
      exact hnot hy
    have hpos : 0 < supDist z y := Nat.pos_of_ne_zero (by
      intro hzero
      exact hne ((supDist_eq_zero_iff z y).mp hzero))
    have hdist : supDist z y = 1 := by omega
    exact ⟨hnot, (setDistance_eq_one_iff U z).mpr ⟨hnot, y, hy, hdist⟩⟩
  · rintro ⟨hnot, hdist⟩
    obtain ⟨_, y, hy, hzy⟩ := (setDistance_eq_one_iff U z).mp hdist
    exact ⟨⟨y, hy, (mem_starBall_iff z y).mpr (by omega)⟩, hnot⟩

#print axioms main

end AKLT.W.WIN012
