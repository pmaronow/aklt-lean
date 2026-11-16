import AKLT.Blueprint.Mom.NodesMean

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Mom

namespace AKLT.W.MOM018

private theorem goldenRatio_sq : goldenRatio ^ 2 = goldenRatio + 1 := by
  unfold goldenRatio
  have hs : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith

private theorem icoRadius_sq : icoRadius ^ 2 = goldenRatio + 2 := by
  unfold icoRadius
  rw [Real.sq_sqrt]
  have hg : 0 ≤ goldenRatio + 2 := by unfold goldenRatio; positivity
  exact hg

private theorem siteU_eq_moment (f : Vec3 → ℝ) :
    siteFunctional .U f = moment f := by
  simp [siteFunctional, Fintype.sum_option, spinWeight, spinVector, moment,
    Finset.mul_sum]

private theorem moment_one : moment (fun _ : Vec3 => 1) = 1 := by
  norm_num [moment, IcoLetter, Fintype.card_prod]

private theorem moment_coord_sq (i : Fin 3) :
    moment (fun v => v i ^ 2) = 1 / 3 := by
  fin_cases i <;>
    simp [moment, IcoLetter, Fintype.sum_prod_type, icoVector, signValue,
      Fin.sum_univ_succ, icoRadius_sq]
  all_goals
    have hphi : 0 < goldenRatio := by unfold goldenRatio; positivity
    have hrad : 0 < goldenRatio + 2 := by linarith
    have hr0 : icoRadius ≠ 0 := by
      have h := Real.sqrt_pos.2 hrad
      simpa [icoRadius] using h.ne'
    have hg0 : goldenRatio + 2 ≠ 0 := hrad.ne'
    field_simp <;> try simp [hr0, hg0]
    rw [icoRadius_sq, goldenRatio_sq]
    ring

private theorem moment_coord_cross (i j : Fin 3) (h : i ≠ j) :
    moment (fun v => v i * v j) = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp_all [moment, IcoLetter, Fintype.sum_prod_type, icoVector, signValue,
      Fin.sum_univ_succ] <;> ring

private def flipLabel (j : IcoLetter) : IcoLetter :=
  (j.1, 1 - j.2.1, 1 - j.2.2)

private def flipEquiv : IcoLetter ≃ IcoLetter where
  toFun := flipLabel
  invFun := flipLabel
  left_inv := by
    intro j
    rcases j with ⟨k, ⟨x, y⟩⟩
    simp [flipLabel]
  right_inv := by
    intro j
    rcases j with ⟨k, ⟨x, y⟩⟩
    simp [flipLabel]

private theorem ico_flip (j : IcoLetter) : icoVector (flipLabel j) = -icoVector j := by
  rcases j with ⟨k, ⟨x, y⟩⟩
  funext i
  fin_cases k <;> fin_cases x <;> fin_cases y <;> fin_cases i <;>
    simp [flipLabel, icoVector, signValue] <;> ring

private theorem moment_odd (f : Vec3 → ℝ) (hf : ∀ v, f (-v) = -f v) :
    moment f = 0 := by
  have hsum : (∑ j : IcoLetter, f (icoVector j)) =
      ∑ j : IcoLetter, f (icoVector (flipLabel j)) := by
    exact (Equiv.sum_comp flipEquiv (fun j => f (icoVector j))).symm
  have hneg : (∑ j : IcoLetter, f (icoVector (flipLabel j))) =
      -∑ j : IcoLetter, f (icoVector j) := by
    simp_rw [ico_flip, hf]
    simp
  have hz : (∑ j : IcoLetter, f (icoVector j)) = 0 := by linarith
  unfold moment
  rw [hz]
  ring

private theorem moment_add (f g : Vec3 → ℝ) :
    moment (fun v => f v + g v) = moment f + moment g := by
  unfold moment
  rw [Finset.sum_add_distrib]
  ring

private theorem moment_coord_tensor (i j : Fin 3) :
    moment (fun v => v i * v j) = if i = j then 1 / 3 else 0 := by
  by_cases h : i = j
  · subst j
    simpa [pow_two] using moment_coord_sq i
  · simp [h, moment_coord_cross i j h]

private theorem moment_scale (c : ℝ) (f : Vec3 → ℝ) :
    moment (fun v => c * f v) = c * moment f := by
  unfold moment
  simp only [Finset.mul_sum]
  ring

private theorem moment_fintype_sum {α : Type} [Fintype α] (f : α → Vec3 → ℝ) :
    moment (fun v => ∑ x, f x v) = ∑ x, moment (f x) := by
  unfold moment
  change (1 / 12) * ∑ j : IcoLetter, ∑ x : α, f x (icoVector j) = _
  rw [Finset.sum_comm, Finset.mul_sum]

private theorem moment_double_sum (f : Fin 3 → Fin 3 → Vec3 → ℝ) :
    moment (fun v => ∑ i, ∑ j, f i j v) = ∑ i, ∑ j, moment (f i j) := by
  simp_rw [moment_fintype_sum]

private theorem moment_dot_mul (a b : Vec3) :
    moment (fun v => dot v a * dot v b) = dot a b / 3 := by
  have hexp : ∀ v : Vec3, dot v a * dot v b =
      ∑ i : Fin 3, ∑ j : Fin 3, (a i * b j) * (v i * v j) := by
    intro v
    simp only [dot]
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  calc
    moment (fun v => dot v a * dot v b) =
        moment (fun v => ∑ i : Fin 3, ∑ j : Fin 3,
          (a i * b j) * (v i * v j)) := by
      congr 1
      funext v
      exact hexp v
    _ = ∑ i : Fin 3, ∑ j : Fin 3,
        moment (fun v => (a i * b j) * (v i * v j)) := moment_double_sum _
    _ = dot a b / 3 := by
      simp_rw [moment_scale, moment_coord_tensor]
      simp [dot, Fin.sum_univ_succ]
      <;> ring

private theorem dot_odd (a : Vec3) (v : Vec3) : dot (-v) a = -dot v a := by
  simp [dot, Finset.sum_neg_distrib]

private theorem moment_dot_zero (a : Vec3) : moment (fun v => dot v a) = 0 := by
  apply moment_odd
  intro v
  exact dot_odd a v

private theorem moment_dot_triple_zero (a b c : Vec3) :
    moment (fun v => (dot v a * dot v b) * dot v c) = 0 := by
  apply moment_odd
  intro v
  rw [dot_odd a v, dot_odd b v, dot_odd c v]
  ring

private theorem moment_three_affine (a : Fin 3 → Vec3) :
    moment (fun v => (1 + dot v (a 0)) * (1 + dot v (a 1)) *
      (1 + dot v (a 2))) = 1 +
        (dot (a 0) (a 1) + dot (a 0) (a 2) + dot (a 1) (a 2)) / 3 := by
  have hexp : (fun v => (1 + dot v (a 0)) * (1 + dot v (a 1)) *
      (1 + dot v (a 2))) = (fun v =>
        1 + dot v (a 0) + dot v (a 1) + dot v (a 2) +
          dot v (a 0) * dot v (a 1) +
          dot v (a 0) * dot v (a 2) +
          dot v (a 1) * dot v (a 2) +
          (dot v (a 0) * dot v (a 1)) * dot v (a 2)) := by
    funext v
    ring
  rw [hexp]
  simp_rw [moment_add]
  rw [moment_one]
  simp_rw [moment_dot_zero, moment_dot_mul, moment_dot_triple_zero]
  ring

end AKLT.W.MOM018

theorem AKLT.W.MOM018.main : AKLT.Blueprint.Mom.TripleNormalizerStatement := by
  intro a
  rw [siteU_eq_moment]
  change moment (fun v => ∏ j : Fin 3, (1 + dot v (a j))) =
    1 + tripleP a / 3
  simpa only [Fin.prod_univ_three, tripleP] using moment_three_affine a

#print axioms AKLT.W.MOM018.main
