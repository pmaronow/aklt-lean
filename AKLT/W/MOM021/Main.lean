import AKLT.Blueprint.Mom.NodesMean

noncomputable section
open scoped BigOperators
open AKLT.Defs
open AKLT.Blueprint.Mom

namespace AKLT.W.MOM021

private lemma dot_add_left (x y z : Vec3) :
    dot (x + y) z = dot x z + dot y z := by
  simp [dot, Finset.sum_add_distrib, add_mul]

private lemma dot_add_right (x y z : Vec3) :
    dot x (y + z) = dot x y + dot x z := by
  simp [dot, Finset.sum_add_distrib, mul_add]

private lemma dot_smul_left (r : ℝ) (x y : Vec3) :
    dot (r • x) y = r * dot x y := by
  simp [dot, Finset.mul_sum, mul_left_comm, mul_comm]

private lemma dot_smul_right (r : ℝ) (x y : Vec3) :
    dot x (r • y) = r * dot x y := by
  simp [dot, Finset.mul_sum, mul_left_comm]

private lemma dot_comm' (x y : Vec3) : dot x y = dot y x := by
  simp [dot, mul_comm]

private lemma normSq_linear3 (r s t : ℝ) (x y z : Vec3) :
    normSq (r • x + s • y + t • z) =
      r^2 * normSq x + s^2 * normSq y + t^2 * normSq z +
        2 * (r * s * dot x y + r * t * dot x z + s * t * dot y z) := by
  simp only [normSq, dot_add_right, dot_smul_right, dot_comm']
  ring

theorem main : AKLT.Blueprint.Mom.TripleSOSIdentityStatement := by
  intro a ha
  let x : ℝ := dot (a 0) (a 1)
  let y : ℝ := dot (a 0) (a 2)
  let z : ℝ := dot (a 1) (a 2)
  have hv : tripleV a =
      (5 + z) • a 0 + (5 + y) • a 1 + (5 + x) • a 2 := by
    funext i
    simp [tripleV, x, y, z, smul_eq_mul]
    ring
  rw [hv]
  rw [normSq_linear3 (5 + z) (5 + y) (5 + x) (a 0) (a 1) (a 2)]
  have h0 : normSq (a 0) = 1 := ha 0
  have h1 : normSq (a 1) = 1 := ha 1
  have h2 : normSq (a 2) = 1 := ha 2
  simp only [tripleP, tripleSOS, x, y, z, h0, h1, h2]
  ring

end AKLT.W.MOM021
