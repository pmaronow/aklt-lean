import AKLT.W.REC005.Means

noncomputable section
open scoped BigOperators
open AKLT.Defs

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000

namespace AKLT.W.REC005

lemma dot_comm (a b : Vec3) : dot a b = dot b a := by
  unfold dot
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma normSq_div (v : Vec3) (r : ℝ) :
    normSq (fun i => v i / r) = normSq v / r ^ 2 := by
  simp only [normSq, dot, div_mul_div_comm, pow_two, Finset.sum_div]

lemma normSq_smul (r : ℝ) (v : Vec3) :
    normSq (fun i => r * v i) = r ^ 2 * normSq v := by
  simp only [normSq, dot, Fin.sum_univ_three]
  ring

lemma tripleV_norm (a b c : Vec3) :
    normSq (tripleV a b c) =
      (5 + dot b c)^2 * normSq a + (5 + dot a c)^2 * normSq b +
      (5 + dot a b)^2 * normSq c +
      2 * (5 + dot b c) * (5 + dot a c) * dot a b +
      2 * (5 + dot b c) * (5 + dot a b) * dot a c +
      2 * (5 + dot a c) * (5 + dot a b) * dot b c := by
  simp only [normSq, tripleV, dot, Fin.sum_univ_three]
  ring

lemma unit_triple_sos (a b c : Vec3)
    (ha : normSq a = 1) (hb : normSq b = 1) (hc : normSq c = 1) :
    (9 + 3 * tripleP a b c)^2 - normSq (tripleV a b c) =
      4 * (((1 - dot b c) - (1 - dot a c))^2 +
        ((1 - dot b c) - (1 - dot a b))^2 +
        ((1 - dot a c) - (1 - dot a b))^2) +
      6 * (1 - dot b c) * (1 - dot a c) * (1 - dot a b) := by
  rw [tripleV_norm, ha, hb, hc]
  unfold tripleP
  ring

lemma triple_denominator_lower (a b c : Vec3)
    (ha : normSq a = 1) (hb : normSq b = 1) (hc : normSq c = 1) :
    1 / 2 ≤ moment (tripleWeight a b c) := by
  have h := normSq_nonneg (a + b + c)
  have heq : normSq (a + b + c) = normSq a + normSq b + normSq c + 2 * tripleP a b c := by
    simp only [normSq, dot, tripleP, Pi.add_apply, Fin.sum_univ_three]
    ring
  rw [heq, ha, hb, hc] at h
  rw [triple_normalizer]
  linarith

lemma unit_triple_bound (a b c : Vec3)
    (ha : normSq a = 1) (hb : normSq b = 1) (hc : normSq c = 1) :
    0 ≤ moment (tripleWeight a b c) ∧
    normSq (fun i => moment (fun v => v i * tripleWeight a b c v)) ≤
      (3 / 5 : ℝ)^2 * moment (tripleWeight a b c)^2 := by
  have hab := dot_unit_bounds a b ha hb
  have hac := dot_unit_bounds a c ha hc
  have hbc := dot_unit_bounds b c hb hc
  have hsos := unit_triple_sos a b c ha hb hc
  have hp : 0 ≤ 6 * (1 - dot b c) * (1 - dot a c) * (1 - dot a b) := by
    apply mul_nonneg
    · exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)
    · linarith
  have hV : normSq (tripleV a b c) ≤ (9 + 3 * tripleP a b c)^2 := by
    nlinarith [sq_nonneg ((1 - dot b c) - (1 - dot a c)),
      sq_nonneg ((1 - dot b c) - (1 - dot a b)),
      sq_nonneg ((1 - dot a c) - (1 - dot a b))]
  refine ⟨le_trans (by norm_num) (triple_denominator_lower a b c ha hb hc), ?_⟩
  have hn : (fun i => moment (fun v => v i * tripleWeight a b c v)) =
      fun i => tripleV a b c i / 15 := by
    funext i
    have h := triple_numerator a b c i
    linarith
  rw [hn, normSq_div, triple_normalizer]
  nlinarith

lemma dot_ball_bounds (a b : Vec3) (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) :
    -1 ≤ dot a b ∧ dot a b ≤ 1 := by
  have h := dot_sq_le a b
  have hp : normSq a * normSq b ≤ 1 :=
    (mul_le_mul ha hb (normSq_nonneg b) (by norm_num)).trans_eq (by norm_num)
  constructor <;> nlinarith

lemma zero_triple_bound (a b : Vec3) (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) :
    0 ≤ moment (tripleWeight a b 0) ∧
    normSq (fun i => moment (fun v => v i * tripleWeight a b 0 v)) ≤
      (3 / 5 : ℝ)^2 * moment (tripleWeight a b 0)^2 := by
  have hd := dot_ball_bounds a b ha hb
  have hA : moment (tripleWeight a b 0) = 1 + dot a b / 3 := by
    simp [triple_normalizer, tripleP, dot]
  have hN : (fun i => moment (fun v => v i * tripleWeight a b 0 v)) =
      fun i => (a i + b i) / 3 := by
    funext i
    have h := triple_numerator a b 0 i
    simp [tripleV, dot] at h
    linarith
  have hn : normSq (fun i => a i + b i) = normSq a + normSq b + 2 * dot a b := by
    simp only [normSq, dot, Fin.sum_univ_three]
    ring
  rw [hA, hN, normSq_div, hn]
  constructor <;> nlinarith [sq_nonneg (dot a b)]

lemma spin_norm_le (j : SpinLetter) : normSq (spinVector j) ≤ 1 := by
  cases j with
  | none => simp [spinVector, normSq, dot]
  | some j => exact (ico_unit j).le

lemma letter_triple_bound (a b c : SpinLetter) :
    0 ≤ moment (tripleWeight (spinVector a) (spinVector b) (spinVector c)) ∧
    normSq (fun i => moment (fun v =>
      v i * tripleWeight (spinVector a) (spinVector b) (spinVector c) v)) ≤
      (3 / 5 : ℝ)^2 *
        moment (tripleWeight (spinVector a) (spinVector b) (spinVector c))^2 := by
  cases a with
  | none =>
    have heq : tripleWeight (spinVector none) (spinVector b) (spinVector c) =
        tripleWeight (spinVector b) (spinVector c) 0 := by
      funext v
      simp [tripleWeight, spinVector, dot]
    rw [heq]
    exact zero_triple_bound _ _ (spin_norm_le b) (spin_norm_le c)
  | some a =>
    cases b with
    | none =>
      have heq : tripleWeight (spinVector (some a)) (spinVector none) (spinVector c) =
          tripleWeight (spinVector (some a)) (spinVector c) 0 := by
        funext v
        simp [tripleWeight, spinVector, dot]
      rw [heq]
      exact zero_triple_bound _ _ (spin_norm_le _) (spin_norm_le c)
    | some b =>
      cases c with
      | none => exact zero_triple_bound _ _ (spin_norm_le _) (spin_norm_le _)
      | some c => exact unit_triple_bound _ _ _ (ico_unit a) (ico_unit b) (ico_unit c)

lemma site_U (f : Vec3 → ℝ) : siteFunctional .U f = moment f := by
  simp [siteFunctional, Fintype.sum_option, spinWeight, spinVector, moment, Finset.mul_sum]

lemma site_D (f : Vec3 → ℝ) :
    siteFunctional .D f = (3 / 5) * moment f + (2 / 5) * f 0 := by
  simp [siteFunctional, Fintype.sum_option, spinWeight, spinVector, moment, ← Finset.mul_sum]
  ring

lemma site_letter_triple_bound (s : Status) (a b c : SpinLetter) :
    0 ≤ siteFunctional s (tripleWeight (spinVector a) (spinVector b) (spinVector c)) ∧
    normSq (fun i => siteFunctional s (fun v =>
      v i * tripleWeight (spinVector a) (spinVector b) (spinVector c) v)) ≤
      (3 / 5 : ℝ)^2 *
        siteFunctional s (tripleWeight (spinVector a) (spinVector b) (spinVector c))^2 := by
  have h := letter_triple_bound a b c
  cases s with
  | U => simpa only [site_U] using h
  | D =>
    simp only [site_D, tripleWeight, dot, Pi.zero_apply, zero_mul,
      Finset.sum_const_zero, add_zero, mul_one, one_mul, mul_zero] at *
    rw [normSq_smul]
    constructor <;> nlinarith
  | X => simp [siteFunctional, spinWeight, normSq, dot]

def letterProduct (l : List SpinLetter) (v : Vec3) : ℝ :=
  (l.map (fun j => 1 + dot v (spinVector j))).prod

theorem local_bound (s : Status) (l : List SpinLetter) (hl : l.length ≤ 3) :
    0 ≤ siteFunctional s (letterProduct l) ∧
    normSq (fun i => siteFunctional s (fun v => v i * letterProduct l v)) ≤
      (3 / 5 : ℝ)^2 * siteFunctional s (letterProduct l)^2 := by
  obtain ⟨a, b, c, heq⟩ : ∃ a b c : SpinLetter,
      letterProduct l = tripleWeight (spinVector a) (spinVector b) (spinVector c) := by
    cases l with
    | nil =>
      exact ⟨none, none, none, by funext v; simp [letterProduct, tripleWeight, spinVector, dot]⟩
    | cons a l =>
      cases l with
      | nil =>
        exact ⟨a, none, none, by funext v; simp [letterProduct, tripleWeight, spinVector, dot]⟩
      | cons b l =>
        cases l with
        | nil =>
          exact ⟨a, b, none, by funext v; simp [letterProduct, tripleWeight, spinVector, dot]⟩
        | cons c l =>
          have : l = [] := by
            apply List.length_eq_zero_iff.mp
            simp only [List.length_cons] at hl
            omega
          subst l
          exact ⟨a, b, c, by funext v; simp [letterProduct, tripleWeight, mul_assoc]⟩
  rw [heq]
  exact site_letter_triple_bound s a b c

end AKLT.W.REC005
