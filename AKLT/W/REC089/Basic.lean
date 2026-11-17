import AKLT.Blueprint.Rec.NodesV2Local

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC089

theorem dot_comm (a b : Vec3) : dot a b = dot b a := by
  unfold dot
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem dot_zero_right (a : Vec3) : dot a 0 = 0 := by simp [dot]
theorem dot_zero_left (a : Vec3) : dot 0 a = 0 := by simp [dot]
theorem dot_neg_right (a b : Vec3) : dot a (-b) = -dot a b := by simp [dot]
theorem dot_div_right (a b : Vec3) (c : ℝ) :
    dot a (fun i => b i / c) = dot a b / c := by
  simp [dot, mul_div_assoc, Finset.sum_div]

theorem normSq_nonneg (a : Vec3) : 0 ≤ normSq a := by
  change 0 ≤ ∑ i, a i * a i
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (a i))

theorem ball_factor_nonneg (a b : Vec3) (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) :
    0 ≤ 1 + dot a b := by
  have h := normSq_nonneg (a + b)
  have he : normSq (a + b) = normSq a + normSq b + 2 * dot a b := by
    simp only [normSq, dot, Pi.add_apply, Fin.sum_univ_three]
    ring
  rw [he] at h
  nlinarith

def fixedUnit : UnitVector := ⟨![1, 0, 0], by
  norm_num [normSq, dot, Fin.sum_univ_three]⟩

def negateUnit (e : UnitVector) : UnitVector := ⟨-e.val, by
  simpa [normSq, dot] using e.property⟩

theorem ico_unit (j : IcoLetter) : normSq (icoVector j) = 1 := by
  have h5 : Real.sqrt 5 ^ 2 = (5 : ℝ) := Real.sq_sqrt (by norm_num)
  have hp : goldenRatio ^ 2 = goldenRatio + 1 := by
    unfold goldenRatio
    nlinarith [Real.sqrt_nonneg (5 : ℝ)]
  have hgp : 0 < goldenRatio + 2 := by
    unfold goldenRatio
    positivity
  have hr : icoRadius ^ 2 = goldenRatio + 2 := Real.sq_sqrt hgp.le
  have hr0 : icoRadius ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hgp)
  rcases j with ⟨j, a, b⟩
  fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [normSq, dot, icoVector, signValue, Fin.sum_univ_three] <;>
    field_simp <;> nlinarith

theorem spin_ball (j : SpinLetter) : normSq (spinVector j) ≤ 1 := by
  cases j with
  | none => norm_num [spinVector, normSq, dot]
  | some j => exact le_of_eq (ico_unit j)

theorem spinWeight_nonneg (s : Status) (j : SpinLetter) : 0 ≤ spinWeight s j := by
  cases s <;> cases j <;> norm_num [spinWeight]

theorem site_U_mass : siteFunctional .U (fun _ => 1) = 1 := by
  norm_num [siteFunctional, spinWeight, Fintype.sum_option, IcoLetter,
    Fintype.card_prod]

theorem site_U_mean (i : Fin 3) : siteFunctional .U (fun n => n i) = 0 := by
  fin_cases i <;>
    simp [siteFunctional, spinWeight, spinVector, icoVector, signValue,
      Fintype.sum_option, Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two] <;>
    ring

theorem site_U_affine (v : Vec3) : siteFunctional .U (fun n => 1 + dot n v) = 1 := by
  unfold siteFunctional dot
  simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hm (i : Fin 3) : ∑ j : SpinLetter, spinWeight .U j * spinVector j i = 0 :=
    site_U_mean i
  simp_rw [← mul_assoc, ← Finset.sum_mul, hm, zero_mul]
  simpa [siteFunctional] using site_U_mass

theorem site_D_split (f : Vec3 → ℝ) :
    siteFunctional .D f = (3 / 5) * siteFunctional .U f + (2 / 5) * f 0 := by
  simp [siteFunctional, spinWeight, spinVector, Fintype.sum_option,
    ← Finset.mul_sum]
  ring

theorem ball_slot_split (b : Vec3) (hb : normSq b ≤ 1) :
    ∃ e : UnitVector, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      ∀ n : Vec3, 1 + dot n b =
        t * (1 + dot n e.val) + (1 - t) * (1 + dot n (-e.val)) := by
  have hn := normSq_nonneg b
  by_cases hz : normSq b = 0
  · have hb0 : b = 0 := by
      funext i
      have hsum : ∑ i, b i * b i = 0 := hz
      have hi : b i * b i = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg (b i))).mp hsum i
          (Finset.mem_univ i)
      exact mul_self_eq_zero.mp hi
    refine ⟨fixedUnit, 1 / 2, by norm_num, by norm_num, ?_⟩
    intro n
    rw [hb0, dot_zero_right, dot_neg_right]
    ring
  · let r := Real.sqrt (normSq b)
    have hr : 0 < r := Real.sqrt_pos.mpr (lt_of_le_of_ne hn (Ne.symm hz))
    have hrs : r ^ 2 = normSq b := Real.sq_sqrt hn
    have hr1 : r ≤ 1 := by nlinarith
    let e : UnitVector := ⟨(fun i => b i / r), by
      simp only [normSq, dot, div_mul_div_comm, ← Finset.sum_div]
      change normSq b / (r * r) = 1
      rw [← pow_two, hrs]
      exact div_self hz⟩
    refine ⟨e, (1 + r) / 2, by positivity, by linarith, ?_⟩
    intro n
    change 1 + dot n b = (1 + r) / 2 * (1 + dot n (fun i => b i / r)) +
      (1 - (1 + r) / 2) * (1 + dot n (-(fun i => b i / r)))
    rw [dot_neg_right, dot_div_right]
    field_simp
    <;> ring

#print axioms ball_slot_split
#print axioms ico_unit
#print axioms site_U_affine

end AKLT.W.REC089
