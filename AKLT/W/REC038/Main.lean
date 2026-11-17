module
public import AKLT.Blueprint.Rec.NodesWalk

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC038

private theorem goldenRatio_sq : goldenRatio ^ 2 = goldenRatio + 1 := by
  unfold goldenRatio
  have h : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith

private theorem icoRadius_sq : icoRadius ^ 2 = goldenRatio + 2 := by
  unfold icoRadius
  have hp : 0 ≤ goldenRatio + 2 := by
    unfold goldenRatio
    nlinarith [Real.sqrt_nonneg 5]
  rw [Real.sq_sqrt hp]

private theorem icoRadius_ne : icoRadius ≠ 0 := by
  have h := icoRadius_sq
  have hp : 0 < goldenRatio + 2 := by
    unfold goldenRatio
    positivity
  nlinarith

private theorem ico_moment_first (i : Fin 3) : moment (fun v => v i) = 0 := by
  fin_cases i <;>
    norm_num [moment, icoVector, signValue, Fintype.sum_prod_type,
      Fin.sum_univ_three, Fin.sum_univ_succ] <;>
    field_simp [icoRadius_ne] <;> ring

private theorem ico_moment_second (i j : Fin 3) :
    moment (fun v => v i * v j) = if i = j then 1 / 3 else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [moment, icoVector, signValue, Fintype.sum_prod_type,
      Fin.sum_univ_three, Fin.sum_univ_succ] <;>
    field_simp [icoRadius_ne] <;>
    nlinarith [goldenRatio_sq, icoRadius_sq]

private theorem siteD_as_moment (f : Vec3 → ℝ) :
    siteFunctional .D f = (3 / 5 : ℝ) * moment f + (2 / 5 : ℝ) * f 0 := by
  simp [siteFunctional, Fintype.sum_option, spinWeight, spinVector, moment,
    ← Finset.mul_sum]
  ring

private theorem siteD_first (i : Fin 3) :
    siteFunctional .D (fun v => v i) = 0 := by
  rw [siteD_as_moment, ico_moment_first]
  simp

private theorem siteD_second (i j : Fin 3) :
    siteFunctional .D (fun v => v i * v j) = if i = j then (1 / 5 : ℝ) else 0 := by
  rw [siteD_as_moment, ico_moment_second]
  by_cases h : i = j
  · norm_num [h]
  · norm_num [h]

private theorem siteFunctional_add (s : Status) (f g : Vec3 → ℝ) :
    siteFunctional s (fun n => f n + g n) =
      siteFunctional s f + siteFunctional s g := by
  unfold siteFunctional
  simp only [mul_add, Finset.sum_add_distrib]

private theorem siteFunctional_weighted_sum (s : Status) (c : Fin 3 → ℝ)
    (f : Fin 3 → Vec3 → ℝ) :
    siteFunctional s (fun n => ∑ i, c i * f i n) =
      ∑ i, c i * siteFunctional s (f i) := by
  unfold siteFunctional
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro n hn
  ring

private theorem siteD_dot_left (a : Vec3) :
    siteFunctional .D (fun n => dot a n) = 0 := by
  rw [show (fun n => dot a n) = (fun n => ∑ i, a i * n i) by
    funext n; rfl]
  rw [siteFunctional_weighted_sum]
  simp [siteD_first]

private theorem siteD_dot_product (a u : Vec3) :
    siteFunctional .D (fun n => dot a n * dot n u) =
      (1 / 5 : ℝ) * dot a u := by
  calc
    siteFunctional .D (fun n => dot a n * dot n u) =
        ∑ i : Fin 3, a i * siteFunctional .D (fun n => n i * dot n u) := by
      rw [show (fun n => dot a n * dot n u) =
        (fun n => ∑ i : Fin 3, a i * (n i * dot n u)) by
          funext n; simp [dot, Finset.sum_mul, mul_assoc]]
      exact siteFunctional_weighted_sum .D a (fun i n => n i * dot n u)
    _ = ∑ i : Fin 3, a i *
        (∑ j : Fin 3, u j * siteFunctional .D (fun n => n i * n j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 2
      rw [show (fun n => n i * dot n u) =
        (fun n => ∑ j : Fin 3, u j * (n i * n j)) by
          funext n
          change n i * (∑ j : Fin 3, n j * u j) = _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring]
      exact siteFunctional_weighted_sum .D u (fun j n => n i * n j)
    _ = (1 / 5 : ℝ) * dot a u := by
      simp_rw [siteD_second]
      rw [show (∑ i : Fin 3, a i * (∑ j : Fin 3, u j * (if i = j then (1 / 5 : ℝ) else 0))) =
          ∑ i : Fin 3, (a i * u i) * (1 / 5 : ℝ) by
        apply Finset.sum_congr rfl
        intro i hi
        simp
        ring]
      calc
        (∑ i : Fin 3, (a i * u i) * (1 / 5 : ℝ)) =
            ∑ i : Fin 3, (1 / 5 : ℝ) * (a i * u i) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = (1 / 5 : ℝ) * dot a u := by
          change (∑ i : Fin 3, (1 / 5 : ℝ) * (a i * u i)) =
            (1 / 5 : ℝ) * ∑ i : Fin 3, a i * u i
          rw [Finset.mul_sum]

theorem main : AKLT.Blueprint.Rec.DStepMomentStatement := by
  intro k hk a u
  interval_cases k
  · simpa using siteD_dot_left a
  · simp
    change siteFunctional .D (fun n => dot a n * (1 + dot n (u 0))) =
      (5⁻¹ : ℝ) * dot a (u 0)
    rw [show (fun n => dot a n * (1 + dot n (u 0))) =
      (fun n => dot a n + dot a n * dot n (u 0)) by
        funext n; ring]
    rw [siteFunctional_add, siteD_dot_left, siteD_dot_product]
    ring

end AKLT.W.REC038

