import AKLT.W.MOM019.Main
import AKLT.W.REC002.Moments
import AKLT.W.REC003.Moments

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC042

open AKLT.W.REC002 (siteU siteD integrate_D2)
open AKLT.W.REC003 (site_add site_coord site_const site_D_one)
open AKLT.W.MOM019 (moment_add ico_first moment_linear_dot
  moment_linear_dot_pair moment_local_triple)

theorem siteU_coordinate_one (a : Vec3) (k : Fin 3) :
    siteFunctional .U (fun n => n k * (1 + dot n a)) = a k / 3 := by
  have he : (fun n : Vec3 => n k * (1 + dot n a)) =
      (fun n => n k + n k * dot n a) := by funext n; ring
  rw [siteU, he, moment_add, ico_first, moment_linear_dot]
  ring

theorem siteU_coordinate_two (a b : Vec3) (k : Fin 3) :
    siteFunctional .U (fun n => n k * ((1 + dot n a) * (1 + dot n b))) =
      (a k + b k) / 3 := by
  have he : (fun n : Vec3 => n k * ((1 + dot n a) * (1 + dot n b))) =
      (fun n => n k + n k * dot n a + n k * dot n b +
        n k * dot n a * dot n b) := by funext n; ring
  rw [siteU, he]
  simp only [moment_add, ico_first, moment_linear_dot, moment_linear_dot_pair]
  ring

theorem siteU_coordinate_three (a b c : Vec3) (k : Fin 3) :
    siteFunctional .U (fun n => n k *
      ((1 + dot n a) * ((1 + dot n b) * (1 + dot n c)))) =
      (a k + b k + c k) / 3 +
        (a k * dot b c + b k * dot a c + c k * dot a b) / 15 := by
  rw [siteU]
  simpa [localProduct, Fin.prod_univ_three, mul_assoc] using
    moment_local_triple ![a, b, c] k

/-- The U identity in the coordinate and finite-neighbour form used by the trace. -/
theorem siteU_coordinate_finset {α : Type*} [DecidableEq α]
    (s : Finset α) (hs : s.card ≤ 3) (m : α → Vec3) (k : Fin 3) :
    siteFunctional .U (fun n => n k * ∏ x ∈ s, (1 + dot n (m x))) =
      (1 / 3 : ℝ) * ∑ o ∈ s, m o k *
        siteFunctional .D (fun n => ∏ x ∈ s.erase o, (1 + dot n (m x))) := by
  interval_cases hc : s.card
  · have he : s = ∅ := Finset.card_eq_zero.mp hc
    simp [he, site_coord]
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc
    simp [siteU_coordinate_one, site_const .D (Or.inr rfl), div_eq_mul_inv]
    ring
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hc
    simp [hab, Finset.erase_insert_of_ne, siteU_coordinate_two, site_D_one]
    ring
  · obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hc
    simp [hab, hac, hbc,
      Finset.erase_insert_of_ne, siteU_coordinate_three, integrate_D2]
    ring

theorem siteD_coordinate_one (a : Vec3) (k : Fin 3) :
    siteFunctional .D (fun n => n k * (1 + dot n a)) = a k / 5 := by
  have he : (fun n : Vec3 => n k * (1 + dot n a)) =
      (fun n => n k + n k * dot n a) := by funext n; ring
  rw [siteD, he]
  simp only [moment_add, ico_first, moment_linear_dot, Pi.zero_apply, zero_mul,
    mul_zero, add_zero, zero_add]
  ring

/-- A D departure with at most one bond has no residual site functional. -/
theorem siteD_coordinate_finset {α : Type*} [DecidableEq α]
    (s : Finset α) (hs : s.card ≤ 1) (m : α → Vec3) (k : Fin 3) :
    siteFunctional .D (fun n => n k * ∏ x ∈ s, (1 + dot n (m x))) =
      (1 / 5 : ℝ) * ∑ o ∈ s, m o k := by
  interval_cases hc : s.card
  · have he : s = ∅ := Finset.card_eq_zero.mp hc
    simp [he, site_coord]
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc
    simp [siteD_coordinate_one, div_eq_mul_inv]
    ring

end AKLT.W.REC042
