module
public import AKLT.W.REC021.LocalBounds
public import AKLT.W.REC021.Geometry

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC021

/-- One fiber of the spins outside the three mutually nonadjacent neighbors.
Missing incident factors are represented by zero fields. -/
structure CubicFibre where
  coefficient : ℝ
  coefficient_nonneg : 0 ≤ coefficient
  status : Fin 3 → Status
  status_active : ∀ i, status i = .U ∨ status i = .D
  field : Fin 3 → Fin 3 → Vec3
  field_ball : ∀ i j, normSq (field i j) ≤ 1

def CubicFibre.A (F : CubicFibre) (i : Fin 3) : ℝ :=
  cubicA (F.status i) (F.field i 0) (F.field i 1) (F.field i 2)

def CubicFibre.B (F : CubicFibre) (i : Fin 3) : Vec3 :=
  cubicB (F.status i) (F.field i 0) (F.field i 1) (F.field i 2)

def CubicFibre.mass (F : CubicFibre) : ℝ :=
  F.coefficient * (F.A 0 * F.A 1 * F.A 2)

def CubicFibre.pairMass (F : CubicFibre) : ℝ :=
  F.coefficient * (dot (F.B 0) (F.B 1) * F.A 2 +
    dot (F.B 0) (F.B 2) * F.A 1 + dot (F.B 1) (F.B 2) * F.A 0)

theorem CubicFibre.A_pos (F : CubicFibre) (i : Fin 3) : 0 < F.A i :=
  (cubic_bound _ (F.status_active i) _ _ _ (F.field_ball i 0)
    (F.field_ball i 1) (F.field_ball i 2)).1

theorem CubicFibre.mass_nonneg (F : CubicFibre) : 0 ≤ F.mass :=
  mul_nonneg F.coefficient_nonneg (by exact le_of_lt (mul_pos (mul_pos (F.A_pos 0)
    (F.A_pos 1)) (F.A_pos 2)))

theorem dot_div (a b : Vec3) (x y : ℝ) :
    dot (fun i => a i / x) (fun i => b i / y) = dot a b / (x * y) := by
  simp only [dot, Fin.sum_univ_three]
  ring

theorem CubicFibre.pairMass_lower (F : CubicFibre) :
    -(27 / 50 : ℝ) * F.mass ≤ F.pairMass := by
  let m (j : Fin 3) : Vec3 := fun i => F.B j i / F.A j
  have hb (j : Fin 3) : normSq (m j) ≤ (9 / 25 : ℝ) :=
    cubic_mean_bound _ (F.status_active j) _ _ _ (F.field_ball j 0)
      (F.field_ball j 1) (F.field_ball j 2)
  have hq := triple_mean_lower (m 0) (m 1) (m 2) (hb 0) (hb 1) (hb 2)
  have hp : 0 < F.A 0 * F.A 1 * F.A 2 :=
    mul_pos (mul_pos (F.A_pos 0) (F.A_pos 1)) (F.A_pos 2)
  have hmul := mul_le_mul_of_nonneg_right hq hp.le
  have he : (dot (m 0) (m 1) + dot (m 0) (m 2) + dot (m 1) (m 2)) *
      (F.A 0 * F.A 1 * F.A 2) =
      dot (F.B 0) (F.B 1) * F.A 2 + dot (F.B 0) (F.B 2) * F.A 1 +
        dot (F.B 1) (F.B 2) * F.A 0 := by
    dsimp [m]
    rw [dot_div, dot_div, dot_div]
    field_simp [ne_of_gt (F.A_pos 0), ne_of_gt (F.A_pos 1), ne_of_gt (F.A_pos 2)]
    <;> ring
  rw [he] at hmul
  have h := mul_le_mul_of_nonneg_left hmul F.coefficient_nonneg
  simpa only [CubicFibre.mass, CubicFibre.pairMass, mul_left_comm] using h

#print axioms CubicFibre.A_pos
#print axioms CubicFibre.mass_nonneg
#print axioms CubicFibre.pairMass_lower

end AKLT.W.REC021
