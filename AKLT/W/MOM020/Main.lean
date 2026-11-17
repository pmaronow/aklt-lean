module
public import AKLT.Blueprint.Mom.NodesMean

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.MOM020

private theorem squaredNorm_nonneg (x : Vec3) : 0 ≤ normSq x := by
  change 0 ≤ ∑ i, x i * x i
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))

private theorem normSq_add (x y : Vec3) :
    normSq (fun i => x i + y i) = normSq x + normSq y + 2 * dot x y := by
  simp [normSq, dot, Fin.sum_univ_three]
  ring

private theorem dot_add_left (x y z : Vec3) :
    dot (fun i => x i + y i) z = dot x z + dot y z := by
  simp [dot, Fin.sum_univ_three]
  ring

private theorem unit_dot_bounds (x y : Vec3)
    (hx : normSq x = 1) (hy : normSq y = 1) :
    -1 ≤ dot x y ∧ dot x y ≤ 1 := by
  have hplus : 0 ≤ normSq (fun i => x i + y i) := squaredNorm_nonneg _
  have hminus : 0 ≤ normSq (fun i => x i - y i) := squaredNorm_nonneg _
  rw [normSq_add] at hplus
  have hsub : normSq (fun i => x i - y i) =
      normSq x + normSq y - 2 * dot x y := by
    simp [normSq, dot, Fin.sum_univ_three]
    ring
  rw [hsub] at hminus
  constructor <;> nlinarith

theorem main : AKLT.Blueprint.Mom.TripleGeometryStatement := by
  intro a ha
  have hsum : 0 ≤ normSq (fun i => a 0 i + a 1 i + a 2 i) := squaredNorm_nonneg _
  have hexpand : normSq (fun i => a 0 i + a 1 i + a 2 i) =
      normSq (a 0) + normSq (a 1) + normSq (a 2) +
        2 * (dot (a 0) (a 1) + dot (a 0) (a 2) + dot (a 1) (a 2)) := by
    rw [show (fun i => a 0 i + a 1 i + a 2 i) =
        (fun i => (a 0 i + a 1 i) + a 2 i) by rfl, normSq_add, normSq_add,
      dot_add_left]
    ring
  rw [hexpand, ha 0, ha 1, ha 2] at hsum
  have hLower : (1 / 2 : ℝ) ≤ 1 + AKLT.Blueprint.Mom.tripleP a / 3 := by
    change (1 / 2 : ℝ) ≤ 1 +
      (dot (a 0) (a 1) + dot (a 0) (a 2) + dot (a 1) (a 2)) / 3
    linarith
  have hab := unit_dot_bounds (a 1) (a 2) (ha 1) (ha 2)
  have hac := unit_dot_bounds (a 0) (a 2) (ha 0) (ha 2)
  have hab01 := unit_dot_bounds (a 0) (a 1) (ha 0) (ha 1)
  refine ⟨hLower, ?_, ?_, ?_⟩ <;> linarith

end AKLT.W.MOM020
