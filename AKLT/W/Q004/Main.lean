module
public import AKLT.Blueprint.Q.NodesFrames

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Q

namespace AKLT.W.Q004

theorem main : AKLT.Blueprint.Q.RotationDisplacementStatement := by
  intro k hk₁ hk₂ v hv
  have hk : k = 1 ∨ k = 2 := by omega
  have hvcoord : v = ![v 0, v 1, v 2] := by
    funext i
    fin_cases i <;> simp
  have hunit0 : v 0 * v 0 + (v 1 * v 1 + v 2 * v 2) = 1 := by
    simpa [normSq, dot, Fin.sum_univ_succ] using hv
  have hunit : (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 = 1 := by
    nlinarith [hunit0]
  have hplane : (v 0) ^ 2 + (v 1) ^ 2 ≤ 1 := by
    have hz : 0 ≤ (v 2) ^ 2 := sq_nonneg (v 2)
    nlinarith
  rcases hk with rfl | rfl
  · have hcalc :
        normSq ((frameRotation ^ 1).mulVec v - v) =
          (404 / 10201 : ℝ) * ((v 0) ^ 2 + (v 1) ^ 2) := by
      rw [hvcoord]
      simp [normSq, dot, frameRotation, Fin.sum_univ_succ]
      ring
    rw [hcalc]
    norm_num
    nlinarith [hplane]
  · have hcalc :
        normSq ((frameRotation ^ 2).mulVec v - v) =
          (1600 / 10201 : ℝ) * ((v 0) ^ 2 + (v 1) ^ 2) := by
      rw [hvcoord]
      simp [normSq, dot, frameRotation, Fin.sum_univ_succ, pow_two]
      ring
    rw [hcalc]
    norm_num
    nlinarith [hplane]

end AKLT.W.Q004
