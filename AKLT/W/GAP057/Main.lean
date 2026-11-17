module
public import AKLT.Blueprint.Gap.NodesShell

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section

namespace AKLT.W.GAP057

open AKLT.Defs AKLT.Challenge AKLT.Blueprint.Gap

/-- The exterior site is beyond range one, so the range-one clause of
`RegularSpec` makes the two full laws equal. -/
theorem main : AKLT.Blueprint.Gap.FarBoundaryEqualityStatement := by
  classical
  intro P hP a u y hy hdist η ξ hAgree
  have hLower : (1 : ℕ∞) ≤ setDistance supDist y (↑(square a u) : Set Plane) := by
    rw [setDistance]
    apply le_iInf
    intro z
    have hyz : y ≠ z.val := by
      intro heq
      exact hy (heq ▸ z.property)
    have hpos : 0 < supDist y z.val := by
      by_contra hnot
      have hzero : supDist y z.val = 0 := Nat.eq_zero_of_not_pos hnot
      simp only [supDist, max_eq_zero] at hzero
      have hcoord₁ : y.1 = z.val.1 := by
        exact sub_eq_zero.mp (Int.natAbs_eq_zero.mp hzero.1)
      have hcoord₂ : y.2 = z.val.2 := by
        exact sub_eq_zero.mp (Int.natAbs_eq_zero.mp hzero.2)
      exact hyz (Prod.ext hcoord₁ hcoord₂)
    have hnat : 1 ≤ supDist y z.val := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hpos)
    exact_mod_cast hnat
  have hFar : ¬ setDistance supDist y (↑(square a u) : Set Plane) ≤ 1 := by
    intro hle
    apply hdist
    exact le_antisymm hle hLower
  rcases hP with ⟨_, _, hRangeOne⟩
  apply hRangeOne (square a u) η ξ
  intro x hx hnear
  by_cases hxy : x = y
  · subst x
    exact (hFar hnear).elim
  · exact hAgree x hxy

end AKLT.W.GAP057

#print axioms AKLT.W.GAP057.main
