module
public import AKLT.W.GAP017.Basic

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Gap
attribute [local instance] Classical.propDecidable

namespace AKLT.W.GAP017

section Coordinates
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {S : ι → Type} [∀ i, Fintype (S i)]

/-- The normalized independent reference weight. -/
def productWeight (π : (i : ι) → Weight (S i)) : Weight (Config S) :=
  fun σ => ∏ i, π i (σ i)

/-- Averaging a single coordinate, keeping every other letter fixed. -/
def average (π : (i : ι) → Weight (S i)) (i : ι) (f : Config S → ℂ) :
    Config S → ℂ := fun σ => ∑ a, (π i a : ℂ) * f (Function.update σ i a)

/-- Squared weighted norm. -/
def energy {Ω : Type} [Fintype Ω] (p : Weight Ω) (f : Ω → ℂ) : ℝ :=
  ∑ σ, p σ * Complex.normSq (f σ)

theorem product_probability (π : (i : ι) → Weight (S i))
    (hπ : ∀ i, PositiveProbability (π i)) : PositiveProbability (productWeight π) := by
  classical
  constructor
  · intro σ
    exact Finset.prod_pos fun i _ => (hπ i).1 (σ i)
  · dsimp [productWeight]
    rw [← Fintype.prod_sum]
    simp_rw [(hπ _).2]
    simp

omit [∀ i, Fintype (S i)] in
theorem prod_update_factor {R : Type} [CommSemiring R]
    (w : (i : ι) → S i → R) (i : ι) (σ : Config S) (a : S i) :
    (∏ j, w j (Function.update σ i a j)) =
      w i a * ∏ j ∈ Finset.univ.erase i, w j (σ j) := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- Swap the original and resampled letter. This is an involution. -/
def swapLetter (i : ι) : (Config S × S i) ≃ (Config S × S i) where
  toFun x := (Function.update x.1 i x.2, x.1 i)
  invFun x := (Function.update x.1 i x.2, x.1 i)
  left_inv x := by simp
  right_inv x := by simp

/-- A product weight is stationary under independent coordinate resampling. -/
theorem sum_update {R : Type} [CommSemiring R]
    (w : (i : ι) → S i → R) (i : ι) (hw : ∑ a, w i a = 1)
    (f : Config S → R) :
    (∑ σ, (∏ j, w j (σ j)) * ∑ a, w i a * f (Function.update σ i a)) =
      ∑ σ, (∏ j, w j (σ j)) * f σ := by
  classical
  have h := (swapLetter (S := S) i).sum_comp
    (fun x : Config S × S i =>
      (∏ j, w j (x.1 j)) * w i x.2 * f (Function.update x.1 i x.2))
  simp only [Fintype.sum_prod_type] at h
  have h' :
      (∑ σ, ∑ a, (∏ j, w j (σ j)) * w i a * f σ) =
        ∑ σ, ∑ a, (∏ j, w j (σ j)) * w i a * f (Function.update σ i a) := by
    convert h using 1
    apply Finset.sum_congr rfl
    intro σ _
    apply Finset.sum_congr rfl
    intro a _
    dsimp [swapLetter]
    simp only [Function.update_idem, Function.update_eq_self]
    rw [prod_update_factor]
    rw [← Finset.mul_prod_erase Finset.univ (fun j => w j (σ j))
      (Finset.mem_univ i)]
    ring
  calc
    _ = ∑ σ, ∑ a, (∏ j, w j (σ j)) * w i a * f (Function.update σ i a) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = ∑ σ, ∑ a, (∏ j, w j (σ j)) * w i a * f σ := h'.symm
    _ = _ := by simp [← Finset.sum_mul, ← Finset.mul_sum, hw, mul_assoc]

theorem sum_fiber_singleton {R : Type} [AddCommMonoid R]
    (i : ι) (σ : Config S) (f : Config S → R) :
    (∑ τ, if AgreeOutside {i} σ τ then f τ else 0) =
      ∑ a, f (Function.update σ i a) := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun τ _ => τ i)
  · intro τ hτ
    exact Finset.mem_univ _
  · intro τ hτ ρ hρ heq
    have hτ' := (Finset.mem_filter.mp hτ).2
    have hρ' := (Finset.mem_filter.mp hρ).2
    funext j
    by_cases hj : j = i
    · subst j; exact heq
    · exact (hτ' j (by simpa using hj)).symm.trans (hρ' j (by simpa using hj))
  · intro a _
    refine ⟨Function.update σ i a, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro j hj
    rw [Function.update_of_ne (by simpa using hj)]
  · intro τ hτ
    congr 1
    funext j
    by_cases hj : j = i
    · subst j; simp
    · rw [Function.update_of_ne hj]
      exact ((Finset.mem_filter.mp hτ).2 j (by simpa using hj)).symm

theorem conditional_product_singleton (π : (i : ι) → Weight (S i))
    (hπ : ∀ i, PositiveProbability (π i)) (i : ι) (f : Config S → ℂ) :
    conditionalExpectation (productWeight π) {i} f = average π i f := by
  classical
  funext σ
  unfold conditionalExpectation
  rw [sum_fiber_singleton, sum_fiber_singleton]
  have hpos : 0 < ∏ j ∈ Finset.univ.erase i, π j (σ j) :=
    Finset.prod_pos fun j _ => (hπ j).1 (σ j)
  have hne : ((∏ j ∈ Finset.univ.erase i, π j (σ j) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hpos
  have hsum : (∑ a, (π i a : ℂ)) = 1 := by
    exact_mod_cast (hπ i).2
  simp only [productWeight, prod_update_factor, Complex.ofReal_mul]
  rw [← Finset.sum_mul, hsum, one_mul]
  dsimp [average]
  rw [div_eq_iff hne, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  ring

omit [Fintype ι] in
theorem average_update (π : (i : ι) → Weight (S i)) (i : ι)
    (f : Config S → ℂ) (σ : Config S) (a : S i) :
    average π i f (Function.update σ i a) = average π i f σ := by
  simp [average]

omit [Fintype ι] in
theorem average_sub (π : (i : ι) → Weight (S i)) (i : ι)
    (f g : Config S → ℂ) :
    average π i (fun σ => f σ - g σ) =
      fun σ => average π i f σ - average π i g σ := by
  funext σ
  simp [average, mul_sub, Finset.sum_sub_distrib]

omit [Fintype ι] in
theorem average_commute (π : (i : ι) → Weight (S i)) (i j : ι)
    (f : Config S → ℂ) :
    average π i (average π j f) = average π j (average π i f) := by
  classical
  by_cases hij : i = j
  · subst j; rfl
  funext σ
  simp only [average, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  rw [Function.update_comm hij]
  ring

variable (π : (i : ι) → Weight (S i)) (hπ : ∀ i, PositiveProbability (π i))
include hπ

omit [Fintype ι] in
theorem average_idempotent (i : ι) (f : Config S → ℂ) :
    average π i (average π i f) = average π i f := by
  funext σ
  simp only [average, Function.update_idem]
  rw [← Finset.sum_mul]
  have hsum : (∑ a, (π i a : ℂ)) = 1 := by exact_mod_cast (hπ i).2
  rw [hsum, one_mul]

theorem sum_product_update (i : ι) (f : Config S → ℝ) :
    (∑ σ, productWeight π σ * ∑ a, π i a * f (Function.update σ i a)) =
      ∑ σ, productWeight π σ * f σ :=
  sum_update π i (hπ i).2 f

theorem mean_average (i : ι) (f : Config S → ℂ) :
    complexMean (productWeight π) (average π i f) =
      complexMean (productWeight π) f := by
  have hsum : (∑ a, (π i a : ℂ)) = 1 := by exact_mod_cast (hπ i).2
  simpa only [complexMean, average, productWeight, Complex.ofReal_prod] using
    sum_update (fun j a => (π j a : ℂ)) i hsum f

/-- Orthogonal least squares after averaging one coordinate of a product law. -/
theorem energy_decomp (i : ι) (f h : Config S → ℂ)
    (hh : ∀ σ a, h (Function.update σ i a) = h σ) :
    energy (productWeight π) (fun σ => f σ - h σ) =
      energy (productWeight π) (fun σ => f σ - average π i f σ) +
        energy (productWeight π) (fun σ => average π i f σ - h σ) := by
  classical
  have hs (σ : Config S) := weighted_sq_decomp (π i)
    ⟨fun a => le_of_lt ((hπ i).1 a), (hπ i).2⟩
    (fun a => f (Function.update σ i a)) (h σ)
  have hleft := sum_product_update π hπ i (fun σ => Complex.normSq (f σ - h σ))
  have hright := sum_product_update π hπ i
    (fun σ => Complex.normSq (f σ - average π i f σ))
  simp only [hh] at hleft
  simp only [average_update] at hright
  dsimp [energy]
  rw [← hleft, ← hright, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  rw [← mul_add]
  congr 1
  exact hs σ

theorem energy_nonneg (f : Config S → ℂ) : 0 ≤ energy (productWeight π) f := by
  apply Finset.sum_nonneg
  intro σ _
  exact mul_nonneg (le_of_lt ((product_probability π hπ).1 σ))
    (Complex.normSq_nonneg _)

theorem energy_average_le (i : ι) (f : Config S → ℂ) :
    energy (productWeight π) (average π i f) ≤ energy (productWeight π) f := by
  have hd := energy_decomp π hπ i f (fun _ => 0) (fun _ _ => rfl)
  simp only [sub_zero] at hd
  have hn := energy_nonneg π hπ (fun σ => f σ - average π i f σ)
  linarith

theorem product_singleton_min (i : ι) (f h : Config S → ℂ)
    (hh : ∀ σ τ, AgreeOutside {i} σ τ → h σ = h τ) :
    blockDirichlet (productWeight π) {i} f ≤
      ∑ σ, productWeight π σ * Complex.normSq (f σ - h σ) := by
  have hh' : ∀ σ a, h (Function.update σ i a) = h σ := by
    intro σ a
    symm
    apply hh
    intro j hj
    rw [Function.update_of_ne (by simpa using hj)]
  have hd := energy_decomp π hπ i f h hh'
  have hn := energy_nonneg π hπ (fun σ => average π i f σ - h σ)
  unfold blockDirichlet
  rw [conditional_product_singleton π hπ]
  change energy (productWeight π) (fun σ => f σ - average π i f σ) ≤
    energy (productWeight π) (fun σ => f σ - h σ)
  linarith

end Coordinates
end AKLT.W.GAP017
