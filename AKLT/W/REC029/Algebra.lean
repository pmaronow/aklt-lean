import AKLT.Blueprint.Rec.NodesLocal

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC029

abbrev E3 := EuclideanSpace ℝ (Fin 3)

def asE (v : Vec3) : E3 := WithLp.toLp 2 v

@[simp] theorem asE_apply (v : Vec3) (i : Fin 3) : asE v i = v i := rfl

theorem normSq_eq (v : Vec3) : normSq v = ‖asE v‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [normSq, dot, pow_two]

theorem dot_eq (v w : Vec3) : dot v w = inner ℝ (asE v) (asE w) := by
  simp [dot, PiLp.inner_apply, asE, mul_comm]

theorem normSq_nonneg (v : Vec3) : 0 ≤ normSq v := by
  rw [normSq_eq]
  positivity

theorem dot_comm (v w : Vec3) : dot v w = dot w v := by
  simp [dot, mul_comm]

theorem normSq_scale (c : ℝ) (v : Vec3) :
    normSq (fun i => c * v i) = c ^ 2 * normSq v := by
  simp only [normSq, dot, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem dot_le_one {v w : Vec3} (hv : normSq v = 1) (hw : normSq w = 1) :
    dot v w ≤ 1 := by
  have h := normSq_nonneg (v - w)
  simp only [normSq, dot, Fin.sum_univ_three, Pi.sub_apply] at h hv hw ⊢
  nlinarith

def P (a : Fin 3 → Vec3) : ℝ :=
  dot (a 0) (a 1) + dot (a 0) (a 2) + dot (a 1) (a 2)

def V (a : Fin 3 → Vec3) : Vec3 := fun i =>
  5 * (a 0 i + a 1 i + a 2 i) +
    a 0 i * dot (a 1) (a 2) + a 1 i * dot (a 0) (a 2) +
    a 2 i * dot (a 0) (a 1)

private theorem golden_sq : goldenRatio ^ 2 = goldenRatio + 1 := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  dsimp [goldenRatio]
  nlinarith

private theorem radius_pos : 0 < icoRadius := by
  apply Real.sqrt_pos.2
  dsimp [goldenRatio]
  positivity

private theorem radius_sq : icoRadius ^ 2 = goldenRatio + 2 := by
  apply Real.sq_sqrt
  dsimp [goldenRatio]
  positivity

private theorem radius_four : icoRadius ^ 4 = 5 * goldenRatio ^ 2 := by
  calc
    _ = (icoRadius ^ 2) ^ 2 := by ring
    _ = (goldenRatio + 2) ^ 2 := by rw [radius_sq]
    _ = 5 * goldenRatio ^ 2 := by nlinarith [golden_sq]

private theorem radius_cube : icoRadius ^ 3 = icoRadius * (goldenRatio + 2) := by
  calc
    _ = icoRadius * icoRadius ^ 2 := by ring
    _ = _ := by rw [radius_sq]

private theorem golden_four : goldenRatio ^ 4 = 3 * goldenRatio + 2 := by
  calc
    _ = (goldenRatio ^ 2) ^ 2 := by ring
    _ = (goldenRatio + 1) ^ 2 := by rw [golden_sq]
    _ = _ := by nlinarith [golden_sq]

/-- Direct evaluation of the finite icosahedral law on three affine factors. -/
theorem triple_normalizer (a : Fin 3 → Vec3) :
    siteFunctional .U (localProduct a) = 1 + P a / 3 := by
  simp [siteFunctional, Fintype.sum_option, spinWeight, spinVector,
    localProduct, P, dot, Fin.prod_univ_three, Fintype.sum_prod_type,
    Fin.sum_univ_three, Fin.sum_univ_two, icoVector, signValue]
  field_simp [ne_of_gt radius_pos]
  ring_nf
  simp only [radius_cube, golden_sq]
  ring

/-- The fourth and second moments give the three-factor numerator. -/
theorem triple_numerator (a : Fin 3 → Vec3) (i : Fin 3) :
    15 * siteFunctional .U (fun n => n i * localProduct a n) = V a i := by
  fin_cases i <;>
    simp [siteFunctional, Fintype.sum_option, spinWeight, spinVector,
      localProduct, V, dot, Fin.prod_univ_three, Fintype.sum_prod_type,
      Fin.sum_univ_three, Fin.sum_univ_two, icoVector, signValue] <;>
    field_simp [ne_of_gt radius_pos] <;>
    ring_nf <;>
    simp only [radius_four, radius_sq, golden_four, golden_sq] <;>
    ring_nf <;>
    simp only [golden_sq] <;>
    ring

theorem normSq_combination (a b c : Vec3) (x y z : ℝ) :
    normSq (fun i => x * a i + y * b i + z * c i) =
      x^2 * normSq a + y^2 * normSq b + z^2 * normSq c +
        2*x*y*dot a b + 2*x*z*dot a c + 2*y*z*dot b c := by
  simp only [normSq, dot, Fin.sum_univ_three]
  ring

/-- Positivity of the scalar normalizer for unit triples. -/
theorem unit_normalizer_lower (a : Fin 3 → Vec3) (ha : ∀ j, normSq (a j) = 1) :
    (1 / 2 : ℝ) ≤ siteFunctional .U (localProduct a) := by
  have h := normSq_nonneg (fun i => a 0 i + a 1 i + a 2 i)
  have he := normSq_combination (a 0) (a 1) (a 2) 1 1 1
  simp only [one_mul, one_pow, ha] at he
  rw [he] at h
  rw [triple_normalizer]
  dsimp [P]
  linarith

/-- The three-field sum of squares; all terms on the right are nonnegative. -/
theorem unit_V_bound (a : Fin 3 → Vec3) (ha : ∀ j, normSq (a j) = 1) :
    normSq (V a) ≤ (9 + 3 * P a)^2 := by
  have hX := sub_nonneg.mpr (dot_le_one (ha 1) (ha 2))
  have hY := sub_nonneg.mpr (dot_le_one (ha 0) (ha 2))
  have hZ := sub_nonneg.mpr (dot_le_one (ha 0) (ha 1))
  have hv : V a = fun i =>
      (5 + dot (a 1) (a 2)) * a 0 i +
      (5 + dot (a 0) (a 2)) * a 1 i +
      (5 + dot (a 0) (a 1)) * a 2 i := by
    funext i
    dsimp [V]
    ring
  have hid : (9 + 3 * P a)^2 - normSq (V a) =
      4 * (((1 - dot (a 1) (a 2)) - (1 - dot (a 0) (a 2)))^2 +
        ((1 - dot (a 1) (a 2)) - (1 - dot (a 0) (a 1)))^2 +
        ((1 - dot (a 0) (a 2)) - (1 - dot (a 0) (a 1)))^2) +
      6 * (1 - dot (a 1) (a 2)) * (1 - dot (a 0) (a 2)) *
        (1 - dot (a 0) (a 1)) := by
    rw [hv, normSq_combination]
    simp only [ha]
    dsimp [P]
    ring
  have hnonneg : 0 ≤ (9 + 3 * P a)^2 - normSq (V a) := by
    rw [hid]
    positivity
  linarith

def numerator (s : Status) (W : Vec3 → ℝ) : Vec3 :=
  fun i => siteFunctional s (fun n => n i * W n)

/-- A homogeneous bound, preserved by nonnegative mixtures. -/
def Good (W : Vec3 → ℝ) : Prop :=
  (1 / 2 : ℝ) ≤ siteFunctional .U W ∧
    ‖asE (numerator .U W)‖ ≤ (3 / 5 : ℝ) * siteFunctional .U W

theorem unit_good (a : Fin 3 → Vec3) (ha : ∀ j, normSq (a j) = 1) :
    Good (localProduct a) := by
  refine ⟨unit_normalizer_lower a ha, ?_⟩
  have hV := unit_V_bound a ha
  have hA := unit_normalizer_lower a ha
  have hn : numerator .U (localProduct a) = fun i => (1 / 15 : ℝ) * V a i := by
    funext i
    have h := triple_numerator a i
    dsimp [numerator]
    linarith
  have hN : normSq (numerator .U (localProduct a)) ≤
      ((3 / 5 : ℝ) * siteFunctional .U (localProduct a))^2 := by
    rw [hn, normSq_scale, triple_normalizer]
    nlinarith [hV]
  rw [normSq_eq] at hN
  nlinarith [norm_nonneg (asE (numerator .U (localProduct a)))]

end AKLT.W.REC029
