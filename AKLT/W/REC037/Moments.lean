import AKLT.Blueprint.Rec.NodesWalk

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC037

private theorem sqrt5_sq : (Real.sqrt 5) ^ 2 = 5 := by
  simpa using Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)

private theorem phi_sq : goldenRatio ^ 2 = goldenRatio + 1 := by
  unfold goldenRatio
  nlinarith [sqrt5_sq]

private theorem radius_sq : icoRadius ^ 2 = goldenRatio + 2 := by
  unfold icoRadius
  exact Real.sq_sqrt (by
    have hp : 0 < goldenRatio := by unfold goldenRatio; positivity
    linarith)

theorem moment_second_coord (i : Fin 3) :
    moment (fun v => v i ^ 2) = 1 / 3 := by
  have hp : 0 < goldenRatio := by unfold goldenRatio; positivity
  have hR : icoRadius ≠ 0 := ne_of_gt (by unfold icoRadius; exact Real.sqrt_pos.2 (by linarith))
  fin_cases i <;>
    simp [moment, IcoLetter, Fintype.sum_prod_type, Fin.sum_univ_succ,
      icoVector, signValue] <;>
    field_simp [hR] <;>
    nlinarith [phi_sq, radius_sq]

theorem moment_first_coord (i : Fin 3) : moment (fun v => v i) = 0 := by
  have hR : icoRadius ≠ 0 := ne_of_gt (by
    unfold icoRadius; apply Real.sqrt_pos.2; unfold goldenRatio; positivity)
  fin_cases i <;>
    simp [moment, IcoLetter, Fintype.sum_prod_type, Fin.sum_univ_succ,
      icoVector, signValue] <;>
    field_simp [hR] <;> ring

theorem moment_second_tensor (i j : Fin 3) :
    moment (fun v => v i * v j) = if i = j then 1 / 3 else 0 := by
  by_cases hij : i = j
  · subst j
    simpa [pow_two] using moment_second_coord i
  · have hR : icoRadius ≠ 0 := ne_of_gt (by
      unfold icoRadius; apply Real.sqrt_pos.2; unfold goldenRatio; positivity)
    fin_cases i <;> fin_cases j <;>
      simp [moment, IcoLetter, Fintype.sum_prod_type, Fin.sum_univ_succ,
        icoVector, signValue, hij] <;>
      field_simp [hR] <;> nlinarith [phi_sq, radius_sq]

theorem moment_third_tensor (i j k : Fin 3) :
    moment (fun v => v i * v j * v k) = 0 := by
  have hR : icoRadius ≠ 0 := ne_of_gt (by
    unfold icoRadius; apply Real.sqrt_pos.2; unfold goldenRatio; positivity)
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [moment, IcoLetter, Fintype.sum_prod_type, Fin.sum_univ_succ,
      icoVector, signValue] <;>
    field_simp [hR] <;> ring

private theorem phi_four : goldenRatio ^ 4 = 3 * goldenRatio + 2 := by
  calc
    goldenRatio ^ 4 = (goldenRatio ^ 2) ^ 2 := by ring
    _ = (goldenRatio + 1) ^ 2 := by rw [phi_sq]
    _ = 3 * goldenRatio + 2 := by nlinarith [phi_sq]

private theorem radius_four : icoRadius ^ 4 = 5 * goldenRatio ^ 2 := by
  calc
    icoRadius ^ 4 = (icoRadius ^ 2) ^ 2 := by ring
    _ = (goldenRatio + 2) ^ 2 := by rw [radius_sq]
    _ = 5 * goldenRatio ^ 2 := by nlinarith [phi_sq, phi_four]

set_option maxHeartbeats 1000000 in
theorem moment_four_tensor (i j k l : Fin 3) :
    moment (fun v => v i * v j * v k * v l) =
      ((if i = j ∧ k = l then 1 else 0) + (if i = k ∧ j = l then 1 else 0) +
        (if i = l ∧ j = k then 1 else 0)) / 15 := by
  have hR : icoRadius ≠ 0 := ne_of_gt (by
      unfold icoRadius; apply Real.sqrt_pos.2; unfold goldenRatio; positivity)
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [moment, IcoLetter, Fintype.sum_prod_type, Fin.sum_univ_succ,
      icoVector, signValue] <;>
    field_simp [hR] <;>
    nlinarith [phi_sq, phi_four, radius_sq, radius_four]

theorem siteU_eq_moment (f : Vec3 → ℝ) : siteFunctional .U f = moment f := by
  simp [siteFunctional, Fintype.sum_option, spinWeight, spinVector,
    moment, Finset.mul_sum]

theorem siteD_eq_moment (f : Vec3 → ℝ) :
    siteFunctional .D f = (3 / 5) * moment f + (2 / 5) * f 0 := by
  simp [siteFunctional, Fintype.sum_option, spinWeight, spinVector, moment,
    ← Finset.mul_sum]
  ring

theorem moment_const : moment (fun _ : Vec3 => (1 : ℝ)) = 1 := by
  norm_num [moment, IcoLetter, Fintype.card_prod]

end AKLT.W.REC037
