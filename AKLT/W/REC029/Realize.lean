import AKLT.W.REC029.Ball

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC029

def rotate (R : E3 ≃ₗᵢ[ℝ] E3) (v : Vec3) : Vec3 := fun i => R (asE v) i

@[simp] theorem asE_rotate (R : E3 ≃ₗᵢ[ℝ] E3) (v : Vec3) :
    asE (rotate R v) = R (asE v) := by ext i; rfl

@[simp] theorem rotate_normSq (R : E3 ≃ₗᵢ[ℝ] E3) (v : Vec3) :
    normSq (rotate R v) = normSq v := by
  rw [normSq_eq, asE_rotate, R.norm_map, ← normSq_eq]

@[simp] theorem rotate_dot (R : E3 ≃ₗᵢ[ℝ] E3) (v w : Vec3) :
    dot (rotate R v) (rotate R w) = dot v w := by
  rw [dot_eq, asE_rotate, asE_rotate, R.inner_map_map, ← dot_eq]

theorem V_eq_E (a : Fin 3 → Vec3) :
    asE (V a) = (5 + dot (a 1) (a 2)) • asE (a 0) +
      (5 + dot (a 0) (a 2)) • asE (a 1) +
      (5 + dot (a 0) (a 1)) • asE (a 2) := by
  ext i
  change V a i = _
  simp only [PiLp.add_apply, PiLp.smul_apply, asE_apply, smul_eq_mul]
  dsimp [V]
  ring

theorem mean_eq_E (a : Fin 3 → Vec3) :
    asE (localMean .U a) =
      (15 * siteFunctional .U (localProduct a))⁻¹ • asE (V a) := by
  ext i
  change siteFunctional .U (fun n => n i * localProduct a n) /
    siteFunctional .U (localProduct a) = _
  have hN : siteFunctional .U (fun n => n i * localProduct a n) = V a i / 15 := by
    linarith [triple_numerator a i]
  rw [hN, div_div]
  simp [div_eq_mul_inv, mul_comm]

/-- Covariance only uses the explicit second- and fourth-moment formulas. -/
theorem mean_covariance (R : E3 ≃ₗᵢ[ℝ] E3) (a : Fin 3 → Vec3) :
    asE (localMean .U (fun j => rotate R (a j))) = R (asE (localMean .U a)) := by
  have hA : siteFunctional .U (localProduct (fun j => rotate R (a j))) =
      siteFunctional .U (localProduct a) := by
    simp only [triple_normalizer, P, rotate_dot]
  rw [mean_eq_E, mean_eq_E, hA, V_eq_E, V_eq_E]
  simp only [rotate_dot, asE_rotate, map_add, map_smul]

/-- A polynomial parameter for the paper's symmetric path of triples. -/
def path (x : ℝ) : Fin 3 → Vec3 :=
  ![![1,0,0], ![x, Real.sqrt (1-x^2), 0], ![x, -Real.sqrt (1-x^2), 0]]

def pathMean (x : ℝ) : ℝ := ((2*x+1)*(x+2)) / (5*(x^2+x+1))

theorem path_den_pos (x : ℝ) : 0 < 5*(x^2+x+1) := by
  nlinarith [sq_nonneg (x + 1/2)]

theorem path_unit (x : ℝ) (hx : x ∈ Set.Icc (-1/2 : ℝ) 1) :
    ∀ j, normSq (path x j) = 1 := by
  have hs : 0 ≤ 1 - x^2 := by
    nlinarith [hx.1, hx.2, mul_nonneg (by linarith [hx.1] : 0 ≤ x+1)
      (sub_nonneg.mpr hx.2)]
  have hsq := Real.sq_sqrt hs
  intro j
  fin_cases j
  · norm_num [path, normSq, dot, Fin.sum_univ_three]
  all_goals
    simp [path, normSq, dot, Fin.sum_univ_three]
    nlinarith

theorem path_mean (x : ℝ) (hx : x ∈ Set.Icc (-1/2 : ℝ) 1) :
    localMean .U (path x) = ![pathMean x, 0, 0] := by
  have hs : 0 ≤ 1 - x^2 := by
    nlinarith [hx.1, hx.2, mul_nonneg (by linarith [hx.1] : 0 ≤ x+1)
      (sub_nonneg.mpr hx.2)]
  have hsq := Real.sq_sqrt hs
  have hP : P (path x) = 2*x + 2*x^2 - 1 := by
    simp [P, path, dot, Fin.sum_univ_three]
    nlinarith [hsq]
  have hV : V (path x) = ![2*(2*x+1)*(x+2), 0, 0] := by
    funext i
    fin_cases i <;> simp [V, path, dot, Fin.sum_univ_three]
    all_goals nlinarith [hsq]
  have hA : siteFunctional .U (localProduct (path x)) = 2*(x^2+x+1)/3 := by
    rw [triple_normalizer, hP]
    ring
  have hq : x^2+x+1 ≠ 0 := by nlinarith [path_den_pos x]
  funext i
  change siteFunctional .U (fun n => n i * localProduct (path x) n) /
    siteFunctional .U (localProduct (path x)) = _
  have hN : siteFunctional .U (fun n => n i * localProduct (path x) n) =
      V (path x) i / 15 := by linarith [triple_numerator (path x) i]
  rw [hN, hA, hV]
  fin_cases i <;> simp [pathMean]
  all_goals field_simp [hq]
  all_goals ring

theorem pathMean_continuous : Continuous pathMean := by
  unfold pathMean
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro x
    exact ne_of_gt (path_den_pos x)

/-- Every vector in the radius-3/5 ball is the U mean of three unit fields. -/
theorem realize_mean (m : Vec3) (hm : normSq m ≤ (3/5 : ℝ)^2) :
    ∃ a : Fin 3 → UnitVector,
      0 < siteFunctional .U (localProduct (fun j => (a j).val)) ∧
      localMean .U (fun j => (a j).val) = m := by
  let r := ‖asE m‖
  have hr : 0 ≤ r := norm_nonneg _
  have hr' : r ≤ (3/5 : ℝ) := by
    rw [normSq_eq] at hm
    dsimp [r]
    nlinarith [norm_nonneg (asE m)]
  have hend0 : pathMean (-1/2) = 0 := by norm_num [pathMean]
  have hend1 : pathMean 1 = (3/5 : ℝ) := by norm_num [pathMean]
  have hIV := intermediate_value_Icc (by norm_num : (-1/2 : ℝ) ≤ 1)
    pathMean_continuous.continuousOn
  obtain ⟨x, hx, hxr⟩ := hIV (by simpa only [hend0, hend1, Set.mem_Icc] using And.intro hr hr')
  let v := localMean .U (path x)
  have hnorm : ‖asE v‖ = ‖asE m‖ := by
    have hv : normSq v = r^2 := by
      dsimp [v]
      rw [path_mean x hx]
      simp [normSq, dot, Fin.sum_univ_three, hxr, pow_two]
    rw [normSq_eq] at hv
    dsimp [r] at hv
    nlinarith [norm_nonneg (asE v), norm_nonneg (asE m)]
  let R : E3 ≃ₗᵢ[ℝ] E3 := (ℝ ∙ (asE v - asE m))ᗮ.reflection
  have hRm : R (asE v) = asE m := Submodule.reflection_sub hnorm
  let a : Fin 3 → UnitVector := fun j =>
    ⟨rotate R (path x j), by rw [rotate_normSq]; exact path_unit x hx j⟩
  refine ⟨a, ?_, ?_⟩
  · have ha : ∀ j, normSq ((a j).val) = 1 := fun j => (a j).property
    linarith [unit_normalizer_lower (fun j => (a j).val) ha]
  · have hcov := mean_covariance R (path x)
    have hh : asE (localMean .U (fun j => (a j).val)) = asE m := hcov.trans hRm
    funext i
    exact congrArg (fun e : E3 => e i) hh

end AKLT.W.REC029
