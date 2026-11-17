module
public import AKLT.Blueprint.Gap.NodesFinite

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Gap
namespace AKLT.W.GAP014

set_option maxHeartbeats 800000

private lemma real_center_identity {Ω : Type} [Fintype Ω] (p : Ω → ℝ)
    (hp : ∑ x, p x = 1) (f : Ω → ℝ) (z : ℝ) :
    (∑ x, p x * (f x - z)^2) =
      (∑ x, p x * (f x - ∑ y, p y * f y)^2) + (∑ y, p y * f y - z)^2 := by
  have expand (c : ℝ) : (∑ x, p x * (f x - c)^2) =
      (∑ x, p x * f x ^ 2) - (2*c)*(∑ x, p x * f x) + c^2 := by
    calc
      _ = ∑ x, (p x * f x ^ 2 - (2*c)*(p x*f x) + c^2*p x) := by
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, hp]
        ring
  rw [expand, expand]
  ring

private lemma complex_center_identity {Ω : Type} [Fintype Ω] (p : Weight Ω)
    (hp : ∑ x, p x = 1) (f : Ω → ℂ) (z : ℂ) :
    (∑ x, p x * Complex.normSq (f x - z)) =
      variance p f + Complex.normSq (complexMean p f - z) := by
  have hr := real_center_identity p hp (fun x => (f x).re) z.re
  have hi := real_center_identity p hp (fun x => (f x).im) z.im
  simp only [variance, complexMean, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.re_sum, Complex.im_sum, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    mul_add, Finset.sum_add_distrib, add_zero, ← pow_two] at *
  linarith

private lemma variance_le_center {Ω : Type} [Fintype Ω] (p : Weight Ω)
    (hp : ∑ x, p x = 1) (f : Ω → ℂ) (z : ℂ) :
    variance p f ≤ ∑ x, p x * Complex.normSq (f x - z) := by
  rw [complex_center_identity p hp f z]
  exact le_add_of_nonneg_right (Complex.normSq_nonneg _)

section Conditional
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
  [∀ i, Fintype (S i)]

omit [Fintype ι] [DecidableEq ι] [∀ i, Fintype (S i)] in
private lemma outside_refl (U : Finset ι) (σ : Config S) : AgreeOutside U σ σ := fun _ _ => rfl
omit [Fintype ι] [DecidableEq ι] [∀ i, Fintype (S i)] in
private lemma outside_symm {U : Finset ι} {σ τ : Config S} (h : AgreeOutside U σ τ) :
    AgreeOutside U τ σ := fun x hx => (h x hx).symm
omit [Fintype ι] [DecidableEq ι] [∀ i, Fintype (S i)] in
private lemma outside_trans {U : Finset ι} {σ τ ρ : Config S}
    (h : AgreeOutside U σ τ) (k : AgreeOutside U τ ρ) : AgreeOutside U σ ρ :=
  fun x hx => (h x hx).trans (k x hx)

private def cMass (p : Weight (Config S)) (U : Finset ι) (σ : Config S) : ℝ := by
  classical
  exact ∑ τ, if AgreeOutside U σ τ then p τ else 0

private def cWeight (p : Weight (Config S)) (U : Finset ι) (σ τ : Config S) : ℝ := by
  classical
  exact (if AgreeOutside U σ τ then p τ else 0) / cMass p U σ

private lemma cMass_pos (p : Weight (Config S)) (hp : ∀ σ, 0 < p σ)
    (U : Finset ι) (σ : Config S) : 0 < cMass p U σ := by
  classical
  apply Finset.sum_pos'
  · intro τ _
    exact ite_nonneg (hp τ).le (le_refl 0)
  · exact ⟨σ, Finset.mem_univ _, by simp [outside_refl, hp σ]⟩

private lemma cMass_eq (p : Weight (Config S)) (U : Finset ι) {σ τ : Config S}
    (h : AgreeOutside U σ τ) : cMass p U σ = cMass p U τ := by
  classical
  apply Finset.sum_congr rfl
  intro ρ _
  have he : AgreeOutside U σ ρ ↔ AgreeOutside U τ ρ :=
    ⟨fun k => outside_trans (outside_symm h) k, outside_trans h⟩
  simp only [he]

private lemma cWeight_prob (p : Weight (Config S)) (hp : ∀ σ, 0 < p σ)
    (U : Finset ι) (σ : Config S) : Probability (cWeight p U σ) := by
  classical
  constructor
  · intro τ
    exact div_nonneg (ite_nonneg (hp τ).le (le_refl 0)) (cMass_pos p hp U σ).le
  · unfold cWeight
    rw [← Finset.sum_div]
    exact div_self (cMass_pos p hp U σ).ne'

private lemma cWeight_balance (p : Weight (Config S)) (U : Finset ι) (σ τ : Config S) :
    p σ * cWeight p U σ τ = p τ * cWeight p U τ σ := by
  classical
  by_cases h : AgreeOutside U σ τ
  · rw [cWeight, cWeight, ite_eq_left h, ite_eq_left (outside_symm h), cMass_eq p U h]
    ring
  · have ht : ¬ AgreeOutside U τ σ := fun k => h (outside_symm k)
    simp [cWeight, h, ht]

private lemma cWeight_stationary (p : Weight (Config S)) (hp : ∀ σ, 0 < p σ)
    (U : Finset ι) (g : Config S → ℝ) :
    (∑ σ, p σ * ∑ τ, cWeight p U σ τ * g τ) = ∑ τ, p τ * g τ := by
  calc
    _ = ∑ τ, ∑ σ, (p τ * g τ) * cWeight p U τ σ := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro τ _
      apply Finset.sum_congr rfl
      intro σ _
      rw [← mul_assoc, cWeight_balance p U σ τ]
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro τ _
      rw [← Finset.mul_sum, (cWeight_prob p hp U τ).2, mul_one]

private lemma ce_eq_cMean (p : Weight (Config S)) (U : Finset ι)
    (f : Config S → ℂ) (σ : Config S) :
    conditionalExpectation p U f σ = complexMean (cWeight p U σ) f := by
  classical
  have hd : (cMass p U σ : ℂ) =
      ∑ τ, if AgreeOutside U σ τ then (p τ : ℂ) else 0 := by
    unfold cMass
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro τ _
    split_ifs <;> rfl
  unfold conditionalExpectation complexMean
  rw [← hd]
  calc
    _ = ∑ τ, (if AgreeOutside U σ τ then (p τ : ℂ) * f τ else 0) /
        (cMass p U σ : ℂ) := Finset.sum_div ..
    _ = _ := by
      apply Finset.sum_congr rfl
      intro τ _
      by_cases ht : AgreeOutside U σ τ
      · simp only [cWeight, ht, ite_true, Complex.ofReal_div]
        ring
      · simp [cWeight, ht]

private lemma ce_invariant (p : Weight (Config S)) (U : Finset ι)
    (f : Config S → ℂ) {σ τ : Config S} (h : AgreeOutside U σ τ) :
    conditionalExpectation p U f σ = conditionalExpectation p U f τ := by
  rw [ce_eq_cMean, ce_eq_cMean]
  unfold complexMean
  apply Finset.sum_congr rfl
  intro ρ _
  have he : AgreeOutside U σ ρ ↔ AgreeOutside U τ ρ :=
    ⟨fun k => outside_trans (outside_symm h) k, outside_trans h⟩
  by_cases hρ : AgreeOutside U τ ρ
  · have hσρ := he.mpr hρ
    simp only [cWeight, hρ, hσρ, ite_true, cMass_eq p U h]
  · have hσρ : ¬ AgreeOutside U σ ρ := fun k => hρ (he.mp k)
    simp only [cWeight, hρ, hσρ, ite_false, cMass_eq p U h]

private lemma blockDirichlet_le_center (p : Weight (Config S)) (hp : ∀ σ, 0 < p σ)
    (U : Finset ι) (f h : Config S → ℂ)
    (hh : ∀ σ τ, AgreeOutside U σ τ → h σ = h τ) :
    blockDirichlet p U f ≤ ∑ σ, p σ * Complex.normSq (f σ - h σ) := by
  classical
  have hi (σ : Config S) :
      (∑ τ, cWeight p U σ τ * Complex.normSq (f τ - conditionalExpectation p U f τ)) ≤
      ∑ τ, cWeight p U σ τ * Complex.normSq (f τ - h τ) := by
    have hl := variance_le_center (cWeight p U σ) (cWeight_prob p hp U σ).2 f (h σ)
    rw [variance, ← ce_eq_cMean] at hl
    convert hl using 1 <;> apply Finset.sum_congr rfl <;> intro τ _
    · by_cases hστ : AgreeOutside U σ τ
      · rw [ce_invariant p U f hστ]
      · simp [cWeight, hστ]
    · by_cases hστ : AgreeOutside U σ τ
      · rw [hh σ τ hστ]
      · simp [cWeight, hστ]
  have hi' := Finset.sum_le_sum (s := Finset.univ) (fun σ _ =>
    mul_le_mul_of_nonneg_left (hi σ) (hp σ).le)
  rw [cWeight_stationary p hp U, cWeight_stationary p hp U] at hi'
  exact hi'

lemma ce_sub (p : Weight (Config S)) (U : Finset ι) (f g : Config S → ℂ) :
    conditionalExpectation p U (fun σ => f σ - g σ) =
      fun σ => conditionalExpectation p U f σ - conditionalExpectation p U g σ := by
  classical
  funext σ
  unfold conditionalExpectation
  rw [← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro τ _
  split_ifs <;> ring

private lemma ce_mean (p : Weight (Config S)) (hp : ∀ σ, 0 < p σ)
    (U : Finset ι) (f : Config S → ℂ) :
    complexMean p (conditionalExpectation p U f) = complexMean p f := by
  apply Complex.ext
  · have h := cWeight_stationary p hp U (fun σ => (f σ).re)
    simpa [complexMean, ce_eq_cMean, Complex.re_sum, Complex.im_sum] using h
  · have h := cWeight_stationary p hp U (fun σ => (f σ).im)
    simpa [complexMean, ce_eq_cMean, Complex.re_sum, Complex.im_sum] using h

private lemma ce_energy_identity (p : Weight (Config S)) (hp : ∀ σ, 0 < p σ)
    (U : Finset ι) (f : Config S → ℂ) (z : ℂ) :
    (∑ σ, p σ * Complex.normSq (f σ - z)) = blockDirichlet p U f +
      ∑ σ, p σ * Complex.normSq (conditionalExpectation p U f σ - z) := by
  classical
  have hv (σ : Config S) : variance (cWeight p U σ) f =
      ∑ τ, cWeight p U σ τ * Complex.normSq (f τ - conditionalExpectation p U f τ) := by
    unfold variance
    rw [← ce_eq_cMean]
    apply Finset.sum_congr rfl
    intro τ _
    by_cases ht : AgreeOutside U σ τ
    · rw [ce_invariant p U f ht]
    · simp [cWeight, ht]
  have hid (σ : Config S) := complex_center_identity (cWeight p U σ)
    (cWeight_prob p hp U σ).2 f z
  have hi := congrArg (fun g : Config S → ℝ => ∑ σ, p σ * g σ)
    (funext hid)
  simp_rw [hv, ← ce_eq_cMean, mul_add, Finset.sum_add_distrib] at hi
  rw [cWeight_stationary p hp U, cWeight_stationary p hp U] at hi
  exact hi

lemma ce_energy_le (p : Weight (Config S)) (hp : ∀ σ, 0 < p σ)
    (U : Finset ι) (f : Config S → ℂ) :
    (∑ σ, p σ * Complex.normSq (conditionalExpectation p U f σ)) ≤
      ∑ σ, p σ * Complex.normSq (f σ) := by
  have hi := ce_energy_identity p hp U f 0
  simp only [sub_zero] at hi
  have hn : 0 ≤ blockDirichlet p U f :=
    Finset.sum_nonneg fun σ _ => mul_nonneg (hp σ).le (Complex.normSq_nonneg _)
  linarith

lemma ce_variance_identity (p : Weight (Config S)) (hp : ∀ σ, 0 < p σ)
    (U : Finset ι) (f : Config S → ℂ) :
    variance p f = blockDirichlet p U f + variance p (conditionalExpectation p U f) := by
  have hi := ce_energy_identity p hp U f (complexMean p f)
  simpa only [variance, ce_mean p hp U f] using hi

end Conditional
/-- The finite one-ratio comparison, for any positive reference law with gap one. -/
theorem density_comparison {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ i, Fintype (S i)]
    (q μ : Weight (Config S)) (hq : PositiveProbability q) (hμ : PositiveProbability μ)
    (hgap : PoincareLower q 1) (m M : ℝ) (hm : 0 < m) (hM : 0 < M)
    (hbound : ∀ σ, m * q σ ≤ μ σ ∧ μ σ ≤ M * q σ) :
    PoincareLower μ (m / M) := by
  classical
  intro f
  have hvar : variance μ f ≤ M * variance q f := by
    calc
      _ ≤ ∑ σ, μ σ * Complex.normSq (f σ - complexMean q f) :=
        variance_le_center μ hμ.2 f _
      _ ≤ ∑ σ, (M*q σ) * Complex.normSq (f σ - complexMean q f) :=
        Finset.sum_le_sum fun σ _ =>
          mul_le_mul_of_nonneg_right (hbound σ).2 (Complex.normSq_nonneg _)
      _ = _ := by simp only [variance, mul_assoc, Finset.mul_sum]
  have hdir : m * dirichlet q f ≤ dirichlet μ f := by
    unfold dirichlet
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hc := blockDirichlet_le_center q hq.1 {i} f (conditionalExpectation μ {i} f)
      (fun σ τ h => ce_invariant μ {i} f h)
    calc
      _ ≤ m * ∑ σ, q σ * Complex.normSq (f σ - conditionalExpectation μ {i} f σ) :=
        mul_le_mul_of_nonneg_left hc hm.le
      _ = ∑ σ, (m*q σ) * Complex.normSq (f σ - conditionalExpectation μ {i} f σ) := by
        simp only [mul_assoc, Finset.mul_sum]
      _ ≤ _ := Finset.sum_le_sum fun σ _ =>
        mul_le_mul_of_nonneg_right (hbound σ).1 (Complex.normSq_nonneg _)
  have hg := hgap f
  have hg' : m * variance q f ≤ dirichlet μ f := by
    simp only [one_mul] at hg
    exact (mul_le_mul_of_nonneg_left hg hm.le).trans hdir
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hM).mpr
  nlinarith [mul_le_mul_of_nonneg_left hvar hm.le,
    mul_le_mul_of_nonneg_left hg' hM.le]

end AKLT.W.GAP014
