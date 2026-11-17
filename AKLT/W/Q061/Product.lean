module
public import AKLT.Blueprint.Q.NodesEnergy

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-! Explicit coordinate averages for finite product probabilities. The swap
of a configuration's coordinate with a fresh letter proves stationarity.
Orthogonality then gives the weighted Pythagorean identity. -/

noncomputable section
open scoped BigOperators
open AKLT.Defs Classical

namespace AKLT.W.Q061

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {S : ι → Type*} [∀ x, Fintype (S x)]

def productMass (p : (x : ι) → Weight (S x)) (σ : (x : ι) → S x) : ℝ :=
  ∏ x, p x (σ x)

def siteAverage (p : (x : ι) → Weight (S x)) (x : ι)
    (f : ((x : ι) → S x) → ℂ) (σ : (x : ι) → S x) : ℂ :=
  ∑ a, (p x a : ℂ) * f (Function.update σ x a)

def energy (p : (x : ι) → Weight (S x)) (f : ((x : ι) → S x) → ℂ) : ℝ :=
  ∑ σ, productMass p σ * Complex.normSq (f σ)

theorem productMass_sum (p : (x : ι) → Weight (S x))
    (hp : ∀ x, PositiveProbability (p x)) : ∑ σ, productMass p σ = 1 := by
  change (∑ σ : (x : ι) → S x, ∏ x, p x (σ x)) = 1
  rw [← Fintype.prod_sum]
  simp_rw [(hp _).2]
  simp

omit [DecidableEq ι] in
theorem productMass_pos (p : (x : ι) → Weight (S x))
    (hp : ∀ x, PositiveProbability (p x)) (σ : (x : ι) → S x) :
    0 < productMass p σ :=
  Finset.prod_pos fun x _ => (hp x).1 (σ x)

theorem energy_nonneg (p : (x : ι) → Weight (S x))
    (hp : ∀ x, PositiveProbability (p x)) (f : ((x : ι) → S x) → ℂ) :
    0 ≤ energy p f :=
  Finset.sum_nonneg fun σ _ =>
    mul_nonneg (le_of_lt (productMass_pos p hp σ)) (Complex.normSq_nonneg _)

omit [∀ x, Fintype (S x)] in
theorem productMass_update (p : (x : ι) → Weight (S x)) (x : ι)
    (σ : (x : ι) → S x) (a : S x) :
    productMass p (Function.update σ x a) =
      (∏ y ∈ Finset.univ.erase x, p y (σ y)) * p x a := by
  classical
  unfold productMass
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ x)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro y hy
  rw [Function.update_of_ne (Finset.mem_erase.mp hy).1]

omit [∀ x, Fintype (S x)] in
theorem productMass_balance (p : (x : ι) → Weight (S x)) (x : ι)
    (σ : (x : ι) → S x) (a : S x) :
    productMass p σ * p x a = productMass p (Function.update σ x a) * p x (σ x) := by
  rw [productMass_update]
  have h := productMass_update p x σ (σ x)
  rw [Function.update_eq_self] at h
  rw [h]
  ring

def resampleSwap (x : ι) :
    (((x : ι) → S x) × S x) ≃ (((x : ι) → S x) × S x) where
  toFun z := (Function.update z.1 x z.2, z.1 x)
  invFun z := (Function.update z.1 x z.2, z.1 x)
  left_inv := by
    rintro ⟨σ, a⟩
    simp [Function.update_idem]
  right_inv := by
    rintro ⟨σ, a⟩
    simp [Function.update_idem]

theorem mean_siteAverage (p : (x : ι) → Weight (S x))
    (hp : ∀ x, PositiveProbability (p x)) (x : ι)
    (f : ((x : ι) → S x) → ℂ) :
    complexMean (productMass p) (siteAverage p x f) = complexMean (productMass p) f := by
  unfold complexMean siteAverage
  simp_rw [Finset.mul_sum]
  rw [← Fintype.sum_prod_type']
  calc
    (∑ z : ((x : ι) → S x) × S x,
      (productMass p z.1 : ℂ) * ((p x z.2 : ℂ) * f (Function.update z.1 x z.2))) =
        ∑ z : ((x : ι) → S x) × S x,
          (productMass p (Function.update z.1 x z.2) : ℂ) *
            ((p x (z.1 x) : ℂ) * f (Function.update z.1 x z.2)) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [← mul_assoc, ← mul_assoc]
      congr 1
      exact_mod_cast productMass_balance p x z.1 z.2
    _ = ∑ z : ((x : ι) → S x) × S x,
          (productMass p z.1 : ℂ) * ((p x z.2 : ℂ) * f z.1) :=
      (resampleSwap (S := S) x).sum_comp
        (fun z => (productMass p z.1 : ℂ) * ((p x z.2 : ℂ) * f z.1))
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro σ _
      dsimp only
      rw [← Finset.mul_sum, ← Finset.sum_mul]
      have h : ∑ a, (p x a : ℂ) = 1 := by exact_mod_cast (hp x).2
      rw [h, one_mul]

omit [Fintype ι] in
theorem siteAverage_update (p : (x : ι) → Weight (S x)) (x : ι)
    (f : ((x : ι) → S x) → ℂ) (σ : (x : ι) → S x) (a : S x) :
    siteAverage p x f (Function.update σ x a) = siteAverage p x f σ := by
  simp [siteAverage, Function.update_idem]

omit [Fintype ι] in
theorem siteAverage_sub (p : (x : ι) → Weight (S x)) (x : ι)
    (f g : ((x : ι) → S x) → ℂ) :
    siteAverage p x (f - g) = siteAverage p x f - siteAverage p x g := by
  ext σ
  simp [siteAverage, mul_sub, Finset.sum_sub_distrib]

omit [Fintype ι] in
theorem siteAverage_idem (p : (x : ι) → Weight (S x))
    (hp : ∀ x, PositiveProbability (p x)) (x : ι)
    (f : ((x : ι) → S x) → ℂ) :
    siteAverage p x (siteAverage p x f) = siteAverage p x f := by
  ext σ
  simp only [siteAverage, Function.update_idem]
  rw [← Finset.sum_mul]
  have h : ∑ a, (p x a : ℂ) = 1 := by exact_mod_cast (hp x).2
  rw [h, one_mul]

omit [Fintype ι] in
theorem siteAverage_commute (p : (x : ι) → Weight (S x)) (x y : ι)
    (f : ((x : ι) → S x) → ℂ) :
    siteAverage p x (siteAverage p y f) = siteAverage p y (siteAverage p x f) := by
  classical
  by_cases h : x = y
  · subst y; rfl
  ext σ
  simp only [siteAverage, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [Function.update_comm h]
  ring

omit [Fintype ι] in
theorem siteAverage_const (p : (x : ι) → Weight (S x))
    (hp : ∀ x, PositiveProbability (p x)) (x : ι) (c : ℂ) :
    siteAverage p x (fun _ => c) = fun _ => c := by
  ext σ
  unfold siteAverage
  rw [← Finset.sum_mul]
  have h : ∑ a, (p x a : ℂ) = 1 := by exact_mod_cast (hp x).2
  rw [h, one_mul]

theorem mean_const (p : (x : ι) → Weight (S x))
    (hp : ∀ x, PositiveProbability (p x)) (c : ℂ) :
    complexMean (productMass p) (fun _ => c) = c := by
  unfold complexMean
  rw [← Finset.sum_mul]
  have h : ∑ σ, (productMass p σ : ℂ) = 1 := by
    exact_mod_cast productMass_sum p hp
  rw [h, one_mul]

theorem mean_sub (w : Weight ((x : ι) → S x)) (f g : ((x : ι) → S x) → ℂ) :
    complexMean w (f - g) = complexMean w f - complexMean w g := by
  simp [complexMean, mul_sub, Finset.sum_sub_distrib]

omit [Fintype ι] in
theorem siteAverage_mul_fixed (p : (x : ι) → Weight (S x)) (x : ι)
    (f g : ((x : ι) → S x) → ℂ)
    (hg : ∀ σ a, g (Function.update σ x a) = g σ) :
    siteAverage p x (f * g) = siteAverage p x f * g := by
  ext σ
  change (∑ a, (p x a : ℂ) * (f (Function.update σ x a) *
    g (Function.update σ x a))) = (∑ a, (p x a : ℂ) * f (Function.update σ x a)) * g σ
  simp_rw [hg, ← mul_assoc]
  rw [Finset.sum_mul]

theorem mean_cross_zero (p : (x : ι) → Weight (S x))
    (hp : ∀ x, PositiveProbability (p x)) (x : ι)
    (f : ((x : ι) → S x) → ℂ) :
    complexMean (productMass p)
      (fun σ => (f σ - siteAverage p x f σ) * star (siteAverage p x f σ)) = 0 := by
  rw [← mean_siteAverage p hp x]
  change complexMean (productMass p)
    (siteAverage p x ((f - siteAverage p x f) * (fun σ => star (siteAverage p x f σ)))) = 0
  rw [siteAverage_mul_fixed p x _ _ (by intro σ a; rw [siteAverage_update])]
  rw [siteAverage_sub, siteAverage_idem p hp, sub_self]
  simp [complexMean]

theorem energy_split (p : (x : ι) → Weight (S x))
    (hp : ∀ x, PositiveProbability (p x)) (x : ι)
    (f : ((x : ι) → S x) → ℂ) :
    energy p f = energy p (f - siteAverage p x f) + energy p (siteAverage p x f) := by
  have identity (z w : ℂ) : Complex.normSq z =
      Complex.normSq (z - w) + Complex.normSq w + 2 * ((z - w) * star w).re := by
    simp [Complex.normSq_apply, Complex.mul_re]
    ring
  have cross : (∑ σ, productMass p σ *
      ((f σ - siteAverage p x f σ) * star (siteAverage p x f σ)).re) = 0 := by
    have h := congrArg Complex.re (mean_cross_zero p hp x f)
    simpa [complexMean, Complex.mul_re] using h
  unfold energy
  conv_lhs =>
    arg 2
    ext σ
    rw [identity (f σ) (siteAverage p x f σ), mul_add, mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hcross : (∑ σ, productMass p σ *
      (2 * ((f σ - siteAverage p x f σ) * star (siteAverage p x f σ)).re)) = 0 := by
    simp_rw [mul_left_comm (productMass p _) 2]
    rw [← Finset.mul_sum, cross, mul_zero]
  rw [hcross, add_zero]
  rfl

theorem sum_fiber {M : Type*} [AddCommMonoid M] (x : ι)
    (σ : (x : ι) → S x) (F : ((x : ι) → S x) → M) :
    (∑ τ, if AgreeOutside {x} σ τ then F τ else 0) =
      ∑ a, F (Function.update σ x a) := by
  classical
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun τ _ => τ x) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro τ hτ ξ hξ he
    apply funext
    intro y
    by_cases hy : y = x
    · subst y; exact he
    · exact ((Finset.mem_filter.mp hτ).2 y (by simpa)).symm.trans
        ((Finset.mem_filter.mp hξ).2 y (by simpa))
  · intro a _
    refine ⟨Function.update σ x a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · intro y hy
      rw [Function.update_of_ne (by simpa using hy)]
    · simp
  · intro τ hτ
    congr 1
    ext y
    by_cases hy : y = x
    · subst y; simp
    · rw [Function.update_of_ne hy]
      exact ((Finset.mem_filter.mp hτ).2 y (by simpa)).symm

theorem conditionalExpectation_singleton (p : (x : ι) → Weight (S x))
    (hp : ∀ x, PositiveProbability (p x)) (x : ι)
    (f : ((x : ι) → S x) → ℂ) (σ : (x : ι) → S x) :
    conditionalExpectation (productMass p) {x} f σ = siteAverage p x f σ := by
  classical
  unfold conditionalExpectation
  rw [sum_fiber, sum_fiber]
  simp_rw [productMass_update, Complex.ofReal_mul, mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  have h : ∑ a, (p x a : ℂ) = 1 := by exact_mod_cast (hp x).2
  rw [h, mul_one]
  have hn : (∏ y ∈ Finset.univ.erase x, p y (σ y) : ℝ) ≠ 0 :=
    ne_of_gt (Finset.prod_pos fun y _ => (hp y).1 (σ y))
  exact mul_div_cancel_left₀ _ (by exact_mod_cast hn)

end AKLT.W.Q061
