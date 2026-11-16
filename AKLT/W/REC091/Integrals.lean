import AKLT.W.REC091.Spin

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC091

theorem siteFunctional_D (f : Vec3 → ℝ) :
    siteFunctional .D f = (3 / 5) * siteFunctional .U f + (2 / 5) * f 0 := by
  simp only [siteFunctional, Fintype.sum_option, spinWeight, spinVector]
  norm_num
  simp only [← Finset.mul_sum]
  ring

theorem integrate_U_three (a b c : Vec3) :
    siteFunctional .U (fun n => (1 + dot n a) * (1 + dot n b) * (1 + dot n c)) =
      1 + (dot a b + dot a c + dot b c) / 3 := by
  have hr : icoRadius ≠ 0 := ne_of_gt icoRadius_pos
  have hc : (1 + goldenRatio ^ 2) / icoRadius ^ 2 = 1 := by
    apply (div_eq_one_iff_eq (pow_ne_zero 2 hr)).mpr
    rw [goldenRatio_sq, icoRadius_sq]
    ring
  calc
    _ = 1 + ((1 + goldenRatio ^ 2) / icoRadius ^ 2) *
        (dot a b + dot a c + dot b c) / 3 := by
      norm_num [siteFunctional, Fintype.sum_option, spinWeight, spinVector,
        Fintype.sum_prod_type, Fin.sum_univ_succ, icoVector, signValue, dot]
      ring
    _ = _ := by rw [hc]; ring

theorem integrate_U_two (a b : Vec3) :
    siteFunctional .U (fun n => (1 + dot n a) * (1 + dot n b)) =
      1 + dot a b / 3 := by
  simpa [dot, Finset.sum_add_distrib] using integrate_U_three a b 0

theorem integrate_U_one (a : Vec3) :
    siteFunctional .U (fun n => 1 + dot n a) = 1 := by
  simpa [dot] using integrate_U_two a 0

theorem integrate_D_two (a b : Vec3) :
    siteFunctional .D (fun n => (1 + dot n a) * (1 + dot n b)) =
      1 + dot a b / 5 := by
  rw [siteFunctional_D, integrate_U_two]
  simp only [dot, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, mul_one]
  ring

theorem integrate_D_one (a : Vec3) :
    siteFunctional .D (fun n => 1 + dot n a) = 1 := by
  simpa [dot] using integrate_D_two a 0

end AKLT.W.REC091
