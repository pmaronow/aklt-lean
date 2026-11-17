module
public import AKLT.W.REC082.Moments

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC082

theorem inv_radius_sq : icoRadius⁻¹ ^ 2 = (3 - goldenRatio) / 5 := by
  have hr : icoRadius ≠ 0 := ne_of_gt icoRadius_pos
  have hp := goldenRatio_sq
  have hrad := icoRadius_sq
  rw [inv_pow]
  apply (eq_div_iff (by norm_num : (5 : ℝ) ≠ 0)).mpr
  apply (inv_mul_eq_iff_eq_mul₀ (pow_ne_zero 2 hr)).mpr
  nlinarith

theorem inv_radius_fourth : icoRadius⁻¹ ^ 4 = (2 - goldenRatio) / 5 := by
  calc
    icoRadius⁻¹ ^ 4 = (icoRadius⁻¹ ^ 2)^2 := by ring
    _ = ((3 - goldenRatio)/5)^2 := by rw [inv_radius_sq]
    _ = (2 - goldenRatio) / 5 := by nlinarith [goldenRatio_sq]

set_option maxHeartbeats 2000000 in
/-- Exact degree-four local identity, verified directly on the thirteen labels. -/
theorem u_step_moment : UStepMomentStatement := by
  intro k hk a u
  have h0 : (Finset.univ : Finset (Fin 0)) = ∅ := by decide
  have h1 : (Finset.univ : Finset (Fin 1)) = {0} := by decide
  have h2 : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  have h3 : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  have e20 : ({0, 1} : Finset (Fin 2)).erase 0 = {1} := by decide
  have e21 : ({0, 1} : Finset (Fin 2)).erase 1 = {0} := by decide
  have e30 : ({0, 1, 2} : Finset (Fin 3)).erase 0 = {1, 2} := by decide
  have e31 : ({0, 1, 2} : Finset (Fin 3)).erase 1 = {0, 2} := by decide
  have e32 : ({0, 1, 2} : Finset (Fin 3)).erase 2 = {0, 1} := by decide
  have hp4 : goldenRatio ^ 4 = 3 * goldenRatio + 2 := by nlinarith [goldenRatio_sq]
  interval_cases k <;>
    norm_num [siteFunctional, Fintype.sum_option, Fintype.sum_prod_type,
      h0, h1, h2, h3, e20, e21, e30, e31, e32, Finset.erase_singleton,
      spinWeight, spinVector, icoVector, signValue, dot] <;>
    ring_nf <;>
    simp only [inv_radius_sq, inv_radius_fourth, goldenRatio_sq, hp4] <;>
    ring_nf <;>
    simp only [goldenRatio_sq] <;> ring

/-- Exact local identity for a D departure with at most one present bond. -/
theorem d_step_moment : DStepMomentStatement := by
  intro k hk a u
  have h0 : (Finset.univ : Finset (Fin 0)) = ∅ := by decide
  have h1 : (Finset.univ : Finset (Fin 1)) = {0} := by decide
  have h2 : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  have h3 : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  interval_cases k <;>
    norm_num [siteFunctional, Fintype.sum_option, Fintype.sum_prod_type,
      h0, h1, h2, h3, spinWeight, spinVector, icoVector, signValue, dot] <;>
    ring_nf <;>
    simp only [inv_radius_sq, goldenRatio_sq] <;>
    ring_nf <;>
    simp only [goldenRatio_sq] <;> ring

end AKLT.W.REC082
