import AKLT.W.REC004.Algebra

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC004

lemma phi_pos : 0 < goldenRatio := by
  unfold goldenRatio
  positivity

lemma phi_sq : goldenRatio ^ 2 = goldenRatio + 1 := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  unfold goldenRatio
  nlinarith

lemma radius_pos : 0 < icoRadius := by
  unfold icoRadius
  exact Real.sqrt_pos.2 (by linarith [phi_pos])

lemma radius_sq : icoRadius ^ 2 = goldenRatio + 2 := by
  exact Real.sq_sqrt (by linarith [phi_pos])

lemma ico_constants :
    (1 / icoRadius : ℝ)^2 + (goldenRatio / icoRadius)^2 = 1 ∧
    (1 / icoRadius : ℝ)^2 * (goldenRatio / icoRadius)^2 = 1 / 5 ∧
    (1 / icoRadius : ℝ)^4 + (goldenRatio / icoRadius)^4 = 3 / 5 := by
  have hr := radius_sq
  have hp := phi_sq
  have hn := ne_of_gt radius_pos
  have h1 : (1 / icoRadius : ℝ)^2 + (goldenRatio / icoRadius)^2 = 1 := by
    field_simp
    nlinarith
  have h2 : (1 / icoRadius : ℝ)^2 * (goldenRatio / icoRadius)^2 = 1 / 5 := by
    field_simp
    nlinarith [sq_nonneg (icoRadius^2 - goldenRatio - 2)]
  refine ⟨h1, h2, ?_⟩
  nlinarith [sq_nonneg ((1 / icoRadius : ℝ)^2 - (goldenRatio / icoRadius)^2)]

lemma ico_unit (j : IcoLetter) : normSq (icoVector j) = 1 := by
  have h := ico_constants.1
  rcases j with ⟨j, k, l⟩
  fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simpa [normSq, dot, Fin.sum_univ_three, icoVector, signValue,
      neg_div, pow_two, add_comm, mul_comm] using h

lemma spin_ball (j : SpinLetter) : normSq (spinVector j) ≤ 1 := by
  cases j with
  | none => norm_num [spinVector, normSq, dot]
  | some j => exact le_of_eq (ico_unit j)

lemma spin_weight_nonneg (s : Status) (j : SpinLetter) : 0 ≤ spinWeight s j := by
  cases s <;> cases j <;> norm_num [spinWeight]

lemma one_add_dot_nonneg {v w : Vec3} (hv : normSq v ≤ 1) (hw : normSq w ≤ 1) :
    0 ≤ 1 + dot v w := by
  have h := (dot_bounds (by norm_num : (0 : ℝ) ≤ 1) hv hw).1
  linarith

/-- The scalar normalizer and vector numerator of a triple of arbitrary fields. -/
def localP (a : Fin 3 → Vec3) : ℝ :=
  dot (a 0) (a 1) + dot (a 0) (a 2) + dot (a 1) (a 2)

def localV (a : Fin 3 → Vec3) : Vec3 := fun i =>
  5 * (a 0 i + a 1 i + a 2 i) +
    a 0 i * dot (a 1) (a 2) + a 1 i * dot (a 0) (a 2) +
    a 2 i * dot (a 0) (a 1)

lemma triple_normalizer (a : Fin 3 → Vec3) :
    siteFunctional .U (localProduct a) = 1 + localP a / 3 := by
  have h := ico_constants.1
  have he : siteFunctional .U (localProduct a) =
      1 + ((1 / icoRadius : ℝ)^2 + (goldenRatio / icoRadius)^2) * localP a / 3 := by
    simp [siteFunctional, Fintype.sum_option, Fintype.sum_prod_type,
      Fin.sum_univ_three, Fin.sum_univ_two, spinWeight, spinVector,
      icoVector, signValue, localProduct, Fin.prod_univ_three,
      dot, localP, neg_div]
    ring
  rw [he, h]
  ring

lemma triple_numerator (a : Fin 3 → Vec3) (i : Fin 3) :
    15 * siteFunctional .U (fun v => v i * localProduct a v) = localV a i := by
  have h1 := ico_constants.1
  have h2 := ico_constants.2.1
  have h4 := ico_constants.2.2
  fin_cases i
  all_goals
    simp [siteFunctional, Fintype.sum_option, Fintype.sum_prod_type,
      Fin.sum_univ_three, Fin.sum_univ_two, spinWeight, spinVector,
      icoVector, signValue, localProduct, Fin.prod_univ_three,
      dot, localV, neg_div]
    ring_nf at h1 h2 h4 ⊢
    grind

lemma normSq_linear3 (u v w : Vec3) (A B C : ℝ) :
    normSq (fun i => A * u i + B * v i + C * w i) =
      A^2 * normSq u + B^2 * normSq v + C^2 * normSq w +
        2*A*B*dot u v + 2*A*C*dot u w + 2*B*C*dot v w := by
  simp [normSq, dot, Fin.sum_univ_three]
  ring

lemma normSq_localV (a : Fin 3 → Vec3) :
    normSq (localV a) =
      (5 + dot (a 1) (a 2))^2 * normSq (a 0) +
      (5 + dot (a 0) (a 2))^2 * normSq (a 1) +
      (5 + dot (a 0) (a 1))^2 * normSq (a 2) +
      2*(5 + dot (a 1) (a 2))*(5 + dot (a 0) (a 2))*dot (a 0) (a 1) +
      2*(5 + dot (a 1) (a 2))*(5 + dot (a 0) (a 1))*dot (a 0) (a 2) +
      2*(5 + dot (a 0) (a 2))*(5 + dot (a 0) (a 1))*dot (a 1) (a 2) := by
  convert normSq_linear3 (a 0) (a 1) (a 2)
    (5 + dot (a 1) (a 2)) (5 + dot (a 0) (a 2)) (5 + dot (a 0) (a 1)) using 2
  funext i
  dsimp [localV]
  ring

lemma normSq_div (v : Vec3) (c : ℝ) :
    normSq (fun i => v i / c) = normSq v / c^2 := by
  simp only [normSq, dot, div_mul_div_comm, ← Finset.sum_div, pow_two]

lemma triple_mean_formula (a : Fin 3 → Vec3) :
    localMean .U a = fun i => localV a i / (15 * (1 + localP a / 3)) := by
  funext i
  dsimp [localMean]
  rw [triple_normalizer]
  have h := triple_numerator a i
  have he : siteFunctional .U (fun v => v i * localProduct a v) = localV a i / 15 := by
    linarith
  rw [he, div_div]

lemma triple_bound_unit (a : Fin 3 → Vec3) (ha : ∀ j, normSq (a j) = 1) :
    1 / 2 ≤ siteFunctional .U (localProduct a) ∧
      normSq (localMean .U a) ≤ (3 / 5 : ℝ)^2 := by
  have hab := dot_bounds (by norm_num : (0 : ℝ) ≤ 1) (le_of_eq (ha 0)) (le_of_eq (ha 1))
  have hac := dot_bounds (by norm_num : (0 : ℝ) ≤ 1) (le_of_eq (ha 0)) (le_of_eq (ha 2))
  have hbc := dot_bounds (by norm_num : (0 : ℝ) ≤ 1) (le_of_eq (ha 1)) (le_of_eq (ha 2))
  have hsum := normSq_nonneg (a 0 + a 1 + a 2)
  have he : normSq (a 0 + a 1 + a 2) = 3 + 2 * localP a := by
    have h := normSq_linear3 (a 0) (a 1) (a 2) 1 1 1
    have hv : a 0 + a 1 + a 2 = (fun i => a 0 i + a 1 i + a 2 i) := rfl
    rw [hv]
    dsimp [localP]
    simp only [one_mul, one_pow, mul_one, ha] at h
    linarith [h]
  have hA : 1 / 2 ≤ 1 + localP a / 3 := by linarith
  have hSOS : (9 + 3 * localP a)^2 - normSq (localV a) =
      4 * ((dot (a 0) (a 1) - dot (a 0) (a 2))^2 +
        (dot (a 0) (a 1) - dot (a 1) (a 2))^2 +
        (dot (a 0) (a 2) - dot (a 1) (a 2))^2) +
      6 * (1 - dot (a 0) (a 1)) * (1 - dot (a 0) (a 2)) *
        (1 - dot (a 1) (a 2)) := by
    rw [normSq_localV]
    simp only [ha, localP]
    ring
  have hnonneg : 0 ≤ (9 + 3 * localP a)^2 - normSq (localV a) := by
    rw [hSOS]
    have hprod := mul_nonneg (mul_nonneg (sub_nonneg.2 hab.2) (sub_nonneg.2 hac.2))
      (sub_nonneg.2 hbc.2)
    nlinarith [sq_nonneg (dot (a 0) (a 1) - dot (a 0) (a 2)),
      sq_nonneg (dot (a 0) (a 1) - dot (a 1) (a 2)),
      sq_nonneg (dot (a 0) (a 2) - dot (a 1) (a 2))]
  refine ⟨by rw [triple_normalizer]; exact hA, ?_⟩
  rw [triple_mean_formula, normSq_div]
  apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < 15 * (1 + localP a / 3)))).2
  nlinarith

lemma dot_zero_left (v : Vec3) : dot 0 v = 0 := by simp [dot]
lemma dot_zero_right (v : Vec3) : dot v 0 = 0 := by simp [dot]
lemma normSq_zero : normSq 0 = 0 := by simp [normSq, dot]

/-- A triple with a zero field is a product of at most two factors. -/
lemma triple_bound_zero (a : Fin 3 → Vec3) (ha : ∀ j, normSq (a j) ≤ 1)
    (hz : a 0 = 0 ∨ a 1 = 0 ∨ a 2 = 0) :
    1 / 2 ≤ siteFunctional .U (localProduct a) ∧
      normSq (localMean .U a) ≤ (3 / 5 : ℝ)^2 := by
  have hnorm := normSq_localV a
  have hnorm0 := normSq_nonneg (a 0)
  have hnorm1 := normSq_nonneg (a 1)
  have hnorm2 := normSq_nonneg (a 2)
  have h01 := dot_bounds (by norm_num : (0 : ℝ) ≤ 1) (ha 0) (ha 1)
  have h02 := dot_bounds (by norm_num : (0 : ℝ) ≤ 1) (ha 0) (ha 2)
  have h12 := dot_bounds (by norm_num : (0 : ℝ) ≤ 1) (ha 1) (ha 2)
  have hA : 1 / 2 ≤ 1 + localP a / 3 := by
    rcases hz with hz | hz | hz <;>
      simp only [localP, hz, dot_zero_left, dot_zero_right, zero_add, add_zero] <;> linarith
  refine ⟨by rw [triple_normalizer]; exact hA, ?_⟩
  rw [triple_mean_formula, normSq_div]
  apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < 15 * (1 + localP a / 3)))).2
  rcases hz with hz | hz | hz
  all_goals
    simp only [localP, hz, dot_zero_left, dot_zero_right, normSq_zero] at hnorm ⊢
    ring_nf at hnorm ⊢
    nlinarith [ha 0, ha 1, ha 2, sq_nonneg (dot (a 0) (a 1) + 1),
      sq_nonneg (dot (a 0) (a 2) + 1), sq_nonneg (dot (a 1) (a 2) + 1)]

lemma triple_bound_atoms (a : Fin 3 → Vec3)
    (ha : ∀ j, normSq (a j) = 1 ∨ a j = 0) :
    1 / 2 ≤ siteFunctional .U (localProduct a) ∧
      normSq (localMean .U a) ≤ (3 / 5 : ℝ)^2 := by
  by_cases h : ∀ j, normSq (a j) = 1
  · exact triple_bound_unit a h
  · have hball : ∀ j, normSq (a j) ≤ 1 := by
      intro j
      rcases ha j with h | h
      · exact le_of_eq h
      · simp [h, normSq_zero]
    have hz : a 0 = 0 ∨ a 1 = 0 ∨ a 2 = 0 := by
      by_contra hn
      apply h
      intro j
      fin_cases j <;> grind
    exact triple_bound_zero a hball hz

lemma site_U_D (f : Vec3 → ℝ) :
    siteFunctional .D f = (3 / 5 : ℝ) * siteFunctional .U f + (2 / 5) * f 0 := by
  simp [siteFunctional, Fintype.sum_option, spinWeight, spinVector, ← Finset.mul_sum]
  ring

lemma localProduct_zero {k : ℕ} (a : Fin k → Vec3) : localProduct a 0 = 1 := by
  simp [localProduct, dot]

lemma normSq_scale (v : Vec3) (t : ℝ) :
    normSq (fun i => t * v i) = t^2 * normSq v := by
  simp [normSq, dot, Fin.sum_univ_three]
  ring

lemma depleted_bound {k : ℕ} (a : Fin k → Vec3)
    (hA : 1 / 2 ≤ siteFunctional .U (localProduct a))
    (hm : normSq (localMean .U a) ≤ (3 / 5 : ℝ)^2) :
    1 / 2 ≤ siteFunctional .D (localProduct a) ∧
      normSq (localMean .D a) ≤ (3 / 5 : ℝ)^2 := by
  let A := siteFunctional .U (localProduct a)
  have hAp : 0 < A := by dsimp [A]; linarith
  have hAn : A ≠ 0 := ne_of_gt hAp
  have hDn : 3 * A + 2 ≠ 0 := by positivity
  have hAD : siteFunctional .D (localProduct a) = (3 * A + 2) / 5 := by
    rw [site_U_D, localProduct_zero]
    dsimp [A]
    ring
  have ht : 0 ≤ 3 * A / (3 * A + 2) ∧ 3 * A / (3 * A + 2) ≤ 1 := by
    constructor
    · positivity
    · apply (div_le_iff₀ (by positivity : 0 < 3 * A + 2)).2
      linarith
  have he : localMean .D a = fun i => (3 * A / (3 * A + 2)) * localMean .U a i := by
    funext i
    simp only [localMean, site_U_D, Pi.zero_apply, mul_zero, add_zero,
      localProduct_zero, mul_one]
    change ((3 / 5) * _) / ((3 / 5) * A + 2 / 5) =
      (3 * A / (3 * A + 2)) * (_ / A)
    field_simp
  refine ⟨by rw [hAD]; dsimp [A]; linarith, ?_⟩
  rw [he, normSq_scale]
  have hnorm := normSq_nonneg (localMean .U a)
  have hs : (3 * A / (3 * A + 2))^2 ≤ 1 := by nlinarith [ht.1, ht.2]
  nlinarith

/-- The only fields used on an unpinned fibre are support atoms (zero included). -/
theorem atom_mean_bound (s : Status) (hs : s = .U ∨ s = .D)
    (a : Fin 3 → SpinLetter) :
    1 / 2 ≤ siteFunctional s (localProduct (fun j => spinVector (a j))) ∧
      normSq (localMean s (fun j => spinVector (a j))) ≤ (3 / 5 : ℝ)^2 := by
  have hb := triple_bound_atoms (fun j => spinVector (a j)) (fun j => by
    cases a j with
    | none => exact Or.inr rfl
    | some k => exact Or.inl (ico_unit k))
  rcases hs with rfl | rfl
  · exact hb
  · exact depleted_bound _ hb.1 hb.2

#print axioms triple_bound_atoms
#print axioms atom_mean_bound

end AKLT.W.REC004
