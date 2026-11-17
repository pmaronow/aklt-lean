module
public import AKLT.Blueprint.Rec.NodesWalk

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC082.PE

private theorem golden_sq : goldenRatio ^ 2 = goldenRatio + 1 := by
  unfold goldenRatio
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  nlinarith

private theorem golden_pos : 0 < goldenRatio := by
  unfold goldenRatio
  positivity

private theorem radius_pos : 0 < icoRadius := by
  unfold icoRadius
  exact Real.sqrt_pos.2 (by linarith [golden_pos])

private theorem radius_sq : icoRadius ^ 2 = goldenRatio + 2 := by
  exact Real.sq_sqrt (by linarith [golden_pos])

private theorem golden_fourth : goldenRatio ^ 4 = 3 * goldenRatio + 2 := by
  nlinarith [golden_sq, sq_nonneg (goldenRatio ^ 2 - goldenRatio - 1)]

private theorem radius_fourth : icoRadius ^ 4 = 5 * goldenRatio + 5 := by
  nlinarith [radius_sq, golden_sq, sq_nonneg (icoRadius ^ 2 - goldenRatio - 2)]

private theorem siteU_first (a : Vec3) :
    siteFunctional .U (fun n => dot a n) = 0 := by
  norm_num [siteFunctional, Fintype.sum_option, spinWeight, spinVector, dot,
    Fintype.sum_prod_type, Fin.sum_univ_succ, icoVector, signValue]
  ring

private theorem siteD_first (a : Vec3) :
    siteFunctional .D (fun n => dot a n) = 0 := by
  norm_num [siteFunctional, Fintype.sum_option, spinWeight, spinVector, dot,
    Fintype.sum_prod_type, Fin.sum_univ_succ, icoVector, signValue]
  ring

private theorem siteU_second (a b : Vec3) :
    siteFunctional .U (fun n => dot a n * dot n b) = dot a b / 3 := by
  norm_num [siteFunctional, Fintype.sum_option, spinWeight, spinVector, dot,
    Fintype.sum_prod_type, Fin.sum_univ_succ, icoVector, signValue]
  field_simp [ne_of_gt radius_pos]
  ring_nf
  simp only [golden_sq, radius_sq]
  ring

private theorem siteD_second (a b : Vec3) :
    siteFunctional .D (fun n => dot a n * dot n b) = dot a b / 5 := by
  norm_num [siteFunctional, Fintype.sum_option, spinWeight, spinVector, dot,
    Fintype.sum_prod_type, Fin.sum_univ_succ, icoVector, signValue]
  field_simp [ne_of_gt radius_pos]
  ring_nf
  simp only [golden_sq, radius_sq]
  ring

private theorem siteD_first_right (a : Vec3) :
    siteFunctional .D (fun n => dot n a) = 0 := by
  simpa only [dot, mul_comm] using siteD_first a

private theorem siteD_second_right (a b : Vec3) :
    siteFunctional .D (fun n => dot n a * dot n b) = dot a b / 5 := by
  have hc (n : Vec3) : dot n a = dot a n := by simp [dot, mul_comm]
  simp_rw [hc]
  exact siteD_second a b

private theorem siteU_third (a b c : Vec3) :
    siteFunctional .U (fun n => dot a n * dot n b * dot n c) = 0 := by
  norm_num [siteFunctional, Fintype.sum_option, spinWeight, spinVector, dot,
    Fintype.sum_prod_type, Fin.sum_univ_succ, icoVector, signValue]
  ring

private theorem siteU_fourth (a b c d : Vec3) :
    siteFunctional .U (fun n => dot a n * dot n b * dot n c * dot n d) =
      (dot a b * dot c d + dot a c * dot b d + dot a d * dot b c) / 15 := by
  norm_num [siteFunctional, Fintype.sum_option, spinWeight, spinVector, dot,
    Fintype.sum_prod_type, Fin.sum_univ_succ, icoVector, signValue]
  field_simp [ne_of_gt radius_pos]
  ring_nf
  simp only [golden_sq, golden_fourth, radius_fourth]
  ring

private theorem site_add (s : Status) (f g : Vec3 → ℝ) :
    siteFunctional s (fun n => f n + g n) = siteFunctional s f + siteFunctional s g := by
  simp [siteFunctional, mul_add, Finset.sum_add_distrib]

private theorem siteD_one : siteFunctional .D (fun _ => (1 : ℝ)) = 1 := by
  norm_num [siteFunctional, Fintype.sum_option, spinWeight, Fintype.card_prod,
    IcoLetter]

/-- The U site identity is proved from the explicit finite support, without
assuming another blueprint leaf. -/
theorem uStepMoment : AKLT.Blueprint.Rec.UStepMomentStatement := by
  intro k hk a u
  interval_cases k
  · simpa using siteU_first a
  · have hu : (Finset.univ : Finset (Fin 1)) = {0} := by decide
    simp only [hu, Finset.prod_singleton, Finset.sum_singleton, Finset.erase_singleton,
      Finset.prod_empty]
    simp only [mul_add, mul_one, site_add,
      siteU_first, siteU_second, siteD_one]
    ring
  · have hu : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
    norm_num [hu, Finset.erase_insert_of_ne, mul_add, add_mul, ← mul_assoc, site_add, siteU_first, siteU_second,
      siteU_third, siteD_first_right, siteD_one]
    ring
  · have hu : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
    norm_num [hu, Finset.erase_insert_of_ne, mul_add, add_mul, ← mul_assoc, site_add, siteU_first, siteU_second,
      siteU_third, siteU_fourth, siteD_first_right, siteD_second_right, siteD_one]
    ring

/-- The D site identity includes the zero-neighbor case. -/
theorem dStepMoment : AKLT.Blueprint.Rec.DStepMomentStatement := by
  intro k hk a u
  interval_cases k
  · simpa using siteD_first a
  · have hu : (Finset.univ : Finset (Fin 1)) = {0} := by decide
    simp only [hu, Finset.prod_singleton, Finset.sum_singleton]
    simp only [mul_add, mul_one, site_add, siteD_first, siteD_second]
    ring

/-- Every geometric support vector has unit norm. -/
theorem ico_unit (j : IcoLetter) : normSq (icoVector j) = 1 := by
  rcases j with ⟨a, b, c⟩
  fin_cases a <;> fin_cases b <;> fin_cases c
  all_goals
    norm_num [normSq, dot, icoVector, signValue, Fin.sum_univ_succ]
    field_simp [ne_of_gt radius_pos]
    nlinarith [golden_sq, radius_sq]

/-- The extra common-support atom is zero; all other atoms are unit vectors. -/
theorem spin_norm_le (j : SpinLetter) : normSq (spinVector j) ≤ 1 := by
  cases j with
  | none => norm_num [spinVector, normSq, dot]
  | some j => exact (ico_unit j).le

end AKLT.W.REC082.PE
