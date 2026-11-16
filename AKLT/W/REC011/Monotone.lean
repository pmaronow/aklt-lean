import AKLT.Blueprint.Rec.NodesResponse

/-! For the free model, coordinate sign symmetry makes every monomial moment
nonnegative, without a degree bound. Natural-coefficient polynomials therefore
give a direct monotonicity argument for bond deletion and depletion. -/

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC011

/-- Removed vertices are represented by a unit atom at zero. -/
def lawWeight (s : Status) (j : SpinLetter) : ℝ :=
  if s = .X then if j = none then 1 else 0 else spinWeight s j

def mono (m : Fin 3 → ℕ) (v : Vec3) : ℝ := ∏ i, v i ^ m i

def lawMoment (s : Status) (m : Fin 3 → ℕ) : ℝ :=
  ∑ j : SpinLetter, lawWeight s j * mono m (spinVector j)

private lemma symmetric_pow_nonneg (x : ℝ) (n : ℕ) :
    0 ≤ x ^ n + (-x) ^ n := by
  rcases Nat.even_or_odd n with h | h
  · rw [h.neg_pow]
    exact add_nonneg (h.pow_nonneg x) (h.pow_nonneg x)
  · rw [h.neg_pow]
    simp

private lemma ico_mono_nonneg (m : Fin 3 → ℕ) : 0 ≤ moment (mono m) := by
  unfold moment
  apply mul_nonneg (by norm_num)
  rw [Fintype.sum_prod_type]
  apply Finset.sum_nonneg
  intro a _
  fin_cases a
  all_goals
    simp [Fintype.sum_prod_type, Fin.sum_univ_succ, Fin.prod_univ_succ,
      icoVector, signValue, mono]
  · convert mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 0) (m 0))
      (mul_nonneg (symmetric_pow_nonneg (1 / icoRadius) (m 1))
        (symmetric_pow_nonneg (goldenRatio / icoRadius) (m 2))) using 1; ring
  · convert mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 0) (m 2))
      (mul_nonneg (symmetric_pow_nonneg (1 / icoRadius) (m 0))
        (symmetric_pow_nonneg (goldenRatio / icoRadius) (m 1))) using 1; ring
  · convert mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 0) (m 1))
      (mul_nonneg (symmetric_pow_nonneg (1 / icoRadius) (m 2))
        (symmetric_pow_nonneg (goldenRatio / icoRadius) (m 0))) using 1; ring

lemma lawMoment_U (m : Fin 3 → ℕ) : lawMoment .U m = moment (mono m) := by
  simp [lawMoment, lawWeight, Fintype.sum_option, spinWeight, spinVector,
    moment, Finset.mul_sum]

lemma lawMoment_D (m : Fin 3 → ℕ) :
    lawMoment .D m = (3 / 5) * moment (mono m) + (2 / 5) * mono m 0 := by
  simp [lawMoment, lawWeight, Fintype.sum_option, spinWeight, spinVector,
    moment, ← Finset.mul_sum]
  ring

lemma lawMoment_X (m : Fin 3 → ℕ) : lawMoment .X m = mono m 0 := by
  simp [lawMoment, lawWeight, spinVector]

lemma mono_zero_cases (m : Fin 3 → ℕ) :
    (mono m 0 = 1 ∧ moment (mono m) = 1) ∨ mono m 0 = 0 := by
  classical
  by_cases h : ∀ i, m i = 0
  · left
    simp [mono, h, moment, IcoLetter, Fintype.card_prod]
  · right
    obtain ⟨i, hi⟩ := not_forall.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

lemma lawMoment_nonneg (s : Status) (m : Fin 3 → ℕ) : 0 ≤ lawMoment s m := by
  have hz : 0 ≤ mono m 0 := Finset.prod_nonneg (fun i _ => pow_nonneg (by simp) _)
  cases s
  · rw [lawMoment_U]; exact ico_mono_nonneg m
  · rw [lawMoment_D]; positivity [ico_mono_nonneg m]
  · rw [lawMoment_X]; exact hz

lemma lawMoment_D_le_U (m : Fin 3 → ℕ) : lawMoment .D m ≤ lawMoment .U m := by
  rw [lawMoment_D, lawMoment_U]
  rcases mono_zero_cases m with ⟨hz, hu⟩ | hz
  · rw [hz, hu]; norm_num
  · rw [hz]; nlinarith [ico_mono_nonneg m]

lemma lawMoment_X_le (s : Status) (m : Fin 3 → ℕ) :
    lawMoment .X m ≤ lawMoment s m := by
  rw [lawMoment_X]
  rcases mono_zero_cases m with ⟨hz, hu⟩ | hz
  · cases s <;> norm_num [lawMoment_U, lawMoment_D, lawMoment_X, hz, hu]
  · rw [hz]; exact lawMoment_nonneg s m

/-- The product law applied to a polynomial with natural coefficients. -/
def polynomialMean {ι : Type*} [Fintype ι] (s : ι → Status)
    (p : MvPolynomial (ι × Fin 3) ℕ) : ℝ := by
  classical
  exact ∑ n : ι → SpinLetter, (∏ x, lawWeight (s x) (n x)) *
    p.eval₂ (Nat.castRingHom ℝ) (fun z => spinVector (n z.1) z.2)

lemma polynomialMean_expansion {ι : Type*} [Fintype ι] (s : ι → Status)
    (p : MvPolynomial (ι × Fin 3) ℕ) :
    polynomialMean s p = ∑ m ∈ p.support, (p.coeff m : ℝ) *
      ∏ x, lawMoment (s x) (fun i => m (x, i)) := by
  classical
  unfold polynomialMean
  simp_rw [MvPolynomial.eval₂_eq', Fintype.prod_prod_type, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  calc
    _ = (p.coeff m : ℝ) * ∑ n : ι → SpinLetter,
        ∏ x, (lawWeight (s x) (n x) * mono (fun i => m (x, i)) (spinVector (n x))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      rw [Finset.prod_mul_distrib]
      change (∏ x, lawWeight (s x) (n x)) *
        ((p.coeff m : ℝ) * ∏ x, mono (fun i => m (x, i)) (spinVector (n x))) = _
      ring
    _ = _ := by
      congr 1
      exact (Fintype.prod_sum fun x j =>
        lawWeight (s x) j * mono (fun i => m (x, i)) (spinVector j)).symm

lemma polynomialMean_nonneg {ι : Type*} [Fintype ι] (s : ι → Status)
    (p : MvPolynomial (ι × Fin 3) ℕ) : 0 ≤ polynomialMean s p := by
  rw [polynomialMean_expansion]
  exact Finset.sum_nonneg fun m _ => mul_nonneg (Nat.cast_nonneg _)
    (Finset.prod_nonneg fun x _ => lawMoment_nonneg _ _)

lemma polynomialMean_add {ι : Type*} [Fintype ι] (s : ι → Status)
    (p q : MvPolynomial (ι × Fin 3) ℕ) :
    polynomialMean s (p + q) = polynomialMean s p + polynomialMean s q := by
  simp [polynomialMean, MvPolynomial.eval₂_add, mul_add, Finset.sum_add_distrib]

lemma polynomialMean_mono {ι : Type*} [Fintype ι] (s t : ι → Status)
    (hst : ∀ x m, lawMoment (s x) m ≤ lawMoment (t x) m)
    (p : MvPolynomial (ι × Fin 3) ℕ) : polynomialMean s p ≤ polynomialMean t p := by
  classical
  rw [polynomialMean_expansion, polynomialMean_expansion]
  apply Finset.sum_le_sum
  intro m _
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact Finset.prod_le_prod₀ (fun x _ => lawMoment_nonneg _ _) (fun x _ => hst x _)

/-- Multiplying further factors `1 + q` adds a polynomial with natural coefficients. -/
lemma prod_one_add_subset {α σ : Type*} [DecidableEq α] (S T : Finset α)
    (hST : S ⊆ T) (q : α → MvPolynomial σ ℕ) :
    ∃ r, (∏ e ∈ T, (1 + q e)) = (∏ e ∈ S, (1 + q e)) + r := by
  classical
  induction T using Finset.induction_on generalizing S with
  | empty =>
      have hS : S = ∅ := Finset.subset_empty.mp hST
      subst S
      exact ⟨0, by simp⟩
  | @insert e T he ih =>
      by_cases hes : e ∈ S
      · obtain ⟨r, hr⟩ := ih (S.erase e) (by
          intro a ha
          exact (Finset.mem_insert.mp (hST (Finset.mem_of_mem_erase ha))).resolve_left
            (Finset.ne_of_mem_erase ha))
        refine ⟨(1 + q e) * r, ?_⟩
        rw [Finset.prod_insert he, hr, mul_add]
        congr 1
        exact (Finset.prod_insert (Finset.notMem_erase e S)
          (f := fun a => 1 + q a)).symm.trans (by rw [Finset.insert_erase hes])
      · obtain ⟨r, hr⟩ := ih S (by
          intro a ha
          exact (Finset.mem_insert.mp (hST ha)).resolve_left (by
            intro h; subst a; exact hes ha))
        refine ⟨r + q e * (∏ a ∈ T, (1 + q a)), ?_⟩
        rw [Finset.prod_insert he, add_mul, one_mul, hr]
        ring

end AKLT.W.REC011
