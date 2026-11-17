module
public import AKLT.W.REC016.Analysis

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC016

theorem golden_sq : goldenRatio ^ 2 = goldenRatio + 1 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  unfold goldenRatio
  nlinarith

theorem radius_pos : 0 < icoRadius := by
  unfold icoRadius goldenRatio
  positivity

theorem radius_sq : icoRadius ^ 2 = goldenRatio + 2 := by
  apply Real.sq_sqrt
  unfold goldenRatio
  positivity

theorem radius_four : icoRadius ^ 4 = 5 * goldenRatio ^ 2 := by
  nlinarith [sq_nonneg (goldenRatio - 1), radius_sq, golden_sq,
    sq_nonneg (icoRadius ^ 2 - (goldenRatio + 2))]

theorem radius_cube : icoRadius ^ 3 = icoRadius * (goldenRatio + 2) := by
  rw [pow_succ, radius_sq]
  ring

theorem golden_four : goldenRatio ^ 4 = 3 * goldenRatio + 2 := by
  nlinarith [golden_sq, sq_nonneg (goldenRatio ^ 2 - (goldenRatio + 1))]

theorem ico_unit (j : IcoLetter) : normSq (icoVector j) = 1 := by
  rcases j with ⟨a,b,c⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [normSq, dot, Fin.sum_univ_three, icoVector, signValue] <;>
    field_simp [radius_pos.ne'] <;> nlinarith [golden_sq, radius_sq]

theorem spin_ball (j : SpinLetter) : normSq (spinVector j) ≤ 1 := by
  cases j with
  | none => norm_num [spinVector, normSq, dot]
  | some j => exact (ico_unit j).le

theorem dot_comm (a b : Vec3) : dot a b = dot b a := by
  simp [dot, mul_comm]

theorem dot_sq_le (a b : Vec3) : dot a b ^ 2 ≤ normSq a * normSq b := by
  simpa [dot, normSq, pow_two] using
    (Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ) (f := a) (g := b))

theorem normSq_nonneg (a : Vec3) : 0 ≤ normSq a := by
  change 0 ≤ ∑ i, a i * a i
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (a i))

theorem ball_dot (a b : Vec3) (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) :
    -1 ≤ dot a b ∧ dot a b ≤ 1 := by
  have h := dot_sq_le a b
  have hp : normSq a * normSq b ≤ 1 :=
    (mul_le_mul ha hb (normSq_nonneg b) (by norm_num)).trans_eq (by norm_num)
  constructor <;> nlinarith

theorem triple_normalizer (a b c : Vec3) :
    siteFunctional .U (fun v => (1 + dot v a) * (1 + dot v b) * (1 + dot v c)) =
      1 + (dot a b + dot a c + dot b c) / 3 := by
  simp only [siteFunctional, Fintype.sum_option, spinWeight, spinVector]
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two,
    icoVector, signValue, dot]
  field_simp [radius_pos.ne']
  ring_nf
  simp only [radius_cube, golden_sq]
  ring

theorem triple_numerator (a b c : Vec3) (i : Fin 3) :
    15 * siteFunctional .U (fun v => v i *
      ((1 + dot v a) * (1 + dot v b) * (1 + dot v c))) =
      5 * (a i + b i + c i) + a i * dot b c + b i * dot a c + c i * dot a b := by
  fin_cases i <;>
    simp only [siteFunctional, Fintype.sum_option, spinWeight, spinVector] <;>
    norm_num [Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two,
      icoVector, signValue, dot] <;>
    field_simp [radius_pos.ne'] <;>
    ring_nf <;>
    simp only [radius_sq, radius_four, golden_four, golden_sq] <;>
    ring_nf <;>
    simp only [golden_sq] <;>
    ring

def tripleVector (a b c : Vec3) : Vec3 := fun i =>
  5 * (a i + b i + c i) + a i * dot b c + b i * dot a c + c i * dot a b

theorem triple_sos (a b c : Vec3) :
    (9 + 3 * (dot a b + dot a c + dot b c)) ^ 2 - normSq (tripleVector a b c) =
      4 * ((dot b c - dot a c)^2 + (dot b c - dot a b)^2 +
        (dot a c - dot a b)^2) +
      6 * (1 - dot a b) * (1 - dot a c) * (1 - dot b c) +
      (1 - normSq a) * (5 + dot b c)^2 +
      (1 - normSq b) * (5 + dot a c)^2 +
      (1 - normSq c) * (5 + dot a b)^2 := by
  simp only [tripleVector, normSq, dot, Fin.sum_univ_three]
  ring

theorem triple_bound (a b c : Vec3)
    (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) (hc : normSq c ≤ 1) :
    let W := fun v => (1 + dot v a) * (1 + dot v b) * (1 + dot v c)
    1 / 2 ≤ siteFunctional .U W ∧
      normSq (fun i => siteFunctional .U (fun v => v i * W v)) ≤
        (3 / 5 * siteFunctional .U W)^2 := by
  dsimp only
  have hsum : normSq (fun i => a i + b i + c i) =
      normSq a + normSq b + normSq c + 2 * (dot a b + dot a c + dot b c) := by
    simp only [normSq, dot, Fin.sum_univ_three]
    ring
  have hlow : 1 / 2 ≤ 1 + (dot a b + dot a c + dot b c) / 3 := by
    have h := normSq_nonneg (fun i => a i + b i + c i)
    rw [hsum] at h
    linarith
  have hsos : 0 ≤ (9 + 3 * (dot a b + dot a c + dot b c)) ^ 2 -
      normSq (tripleVector a b c) := by
    rw [triple_sos]
    have hab := (ball_dot a b ha hb).2
    have hac := (ball_dot a c ha hc).2
    have hbc := (ball_dot b c hb hc).2
    positivity
  have hnum : (fun i => siteFunctional .U (fun v => v i *
      ((1 + dot v a) * (1 + dot v b) * (1 + dot v c)))) =
      fun i => tripleVector a b c i / 15 := by
    funext i
    have h := triple_numerator a b c i
    dsimp [tripleVector]
    linarith
  refine ⟨by rw [triple_normalizer]; exact hlow, ?_⟩
  rw [hnum, triple_normalizer]
  have hnorm : normSq (fun i => tripleVector a b c i / 15) =
      normSq (tripleVector a b c) / 225 := by
    simp [normSq, dot, Fin.sum_univ_three]
    ring
  rw [hnorm]
  nlinarith

theorem normSq_div (v : Vec3) (d : ℝ) :
    normSq (fun i => v i / d) = normSq v / d^2 := by
  simp only [normSq, dot, div_mul_div_comm, ← Finset.sum_div, pow_two]

theorem site_mixture (f : Vec3 → ℝ) :
    siteFunctional .D f = (3 / 5) * siteFunctional .U f + (2 / 5) * f 0 := by
  simp [siteFunctional, Fintype.sum_option, spinWeight, spinVector, ← Finset.mul_sum]
  ring

theorem local_bound {k : ℕ} (hk : k ≤ 3) (a : Fin k → Vec3)
    (ha : ∀ i, normSq (a i) ≤ 1) (s : Status) (hs : s = .U ∨ s = .D) :
    0 < siteFunctional s (localProduct a) ∧ normSq (localMean s a) ≤ (3 / 5 : ℝ)^2 := by
  have hU : 1 / 2 ≤ siteFunctional .U (localProduct a) ∧
      normSq (fun i => siteFunctional .U (fun v => v i * localProduct a v)) ≤
        (3 / 5 * siteFunctional .U (localProduct a))^2 := by
    unfold localProduct
    interval_cases k
    · simpa [localProduct, dot] using
        triple_bound (0 : Vec3) 0 0 (by simp [normSq, dot])
          (by simp [normSq, dot]) (by simp [normSq, dot])
    · simpa [localProduct, Fin.prod_univ_three, dot] using
        triple_bound (a 0) 0 0 (ha 0) (by simp [normSq, dot]) (by simp [normSq, dot])
    · simpa [localProduct, Fin.prod_univ_two, dot] using
        triple_bound (a 0) (a 1) 0 (ha 0) (ha 1) (by simp [normSq, dot])
    · simpa [localProduct, Fin.prod_univ_three, mul_assoc] using
        triple_bound (a 0) (a 1) (a 2) (ha 0) (ha 1) (ha 2)
  have hpos : 0 < siteFunctional .U (localProduct a) := by linarith [hU.1]
  rcases hs with rfl | rfl
  · refine ⟨hpos, ?_⟩
    unfold localMean
    rw [normSq_div]
    apply (div_le_iff₀ (sq_pos_of_pos hpos)).2
    nlinarith [hU.2]
  · have hmass : siteFunctional .D (localProduct a) =
        (3 / 5) * siteFunctional .U (localProduct a) + 2 / 5 := by
      rw [site_mixture]
      simp [localProduct, dot]
    have hnum : (fun i => siteFunctional .D (fun v => v i * localProduct a v)) =
        fun i => (3 / 5) * siteFunctional .U (fun v => v i * localProduct a v) := by
      funext i
      rw [site_mixture]
      simp
    have hnorm : normSq (fun i => (3 / 5) *
        siteFunctional .U (fun v => v i * localProduct a v)) =
        (3 / 5 : ℝ)^2 *
          normSq (fun i => siteFunctional .U (fun v => v i * localProduct a v)) := by
      simp only [normSq, dot, Fin.sum_univ_three]
      ring
    have hposD : 0 < siteFunctional .D (localProduct a) := by rw [hmass]; positivity
    refine ⟨hposD, ?_⟩
    unfold localMean
    rw [normSq_div, hnum, hnorm]
    apply (div_le_iff₀ (sq_pos_of_pos hposD)).2
    rw [hmass]
    nlinarith [hU.2]

theorem small_dot (a b : Vec3) (ha : normSq a ≤ (3 / 5 : ℝ)^2)
    (hb : normSq b ≤ (3 / 5 : ℝ)^2) : -(9 / 25 : ℝ) ≤ dot a b := by
  have hp : normSq a * normSq b ≤ (9 / 25 : ℝ)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb),
      mul_nonneg (normSq_nonneg a) (sub_nonneg.mpr hb)]
  nlinarith [dot_sq_le a b]

#print axioms ico_unit
#print axioms triple_normalizer
#print axioms triple_numerator
#print axioms triple_sos
#print axioms local_bound

end AKLT.W.REC016
