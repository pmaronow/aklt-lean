import AKLT.W.GAP016.Product

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Gap
attribute [local instance] Classical.propDecidable

namespace AKLT.W.GAP016

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {S : ι → Type} [∀ i, Fintype (S i)]

/-- A singleton fibre is parametrized by the letter at that site. -/
lemma single_fibre_sum {R : Type*} [AddCommMonoid R]
    (σ : Config S) (i : ι) (g : Config S → R) :
    (∑ τ, if AgreeOutside {i} σ τ then g τ else 0) =
      ∑ a, g (Function.update σ i a) := by
  classical
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun a _ => Function.update σ i a) ?_ ?_ ?_ ?_
  · intro a _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro j hj
    exact (Function.update_of_ne (by simpa using hj) a σ).symm
  · intro a _ b _ hab
    have h := congrFun hab i
    simpa using h
  · intro τ hτ
    refine ⟨τ i, Finset.mem_univ _, ?_⟩
    ext j
    by_cases hji : j = i
    · subst j
      simp
    · rw [Function.update_of_ne hji]
      exact (Finset.mem_filter.mp hτ).2 j (by simpa using hji)
  · intro a _
    rfl

/-- The explicit conditional quotient agrees with coordinate averaging. -/
lemma conditionalExpectation_product_singleton
    (π : (i : ι) → Weight (S i)) (hπ : ∀ i, PositiveProbability (π i))
    (i : ι) (f : Config S → ℂ) (σ : Config S) :
    conditionalExpectation (productMass π) {i} f σ =
      average (fun j a => (π j a : ℂ)) i f σ := by
  classical
  unfold conditionalExpectation
  rw [single_fibre_sum, single_fibre_sum]
  let c : ℝ := ∏ j ∈ Finset.univ.erase i, π j (σ j)
  have hc : 0 < c := Finset.prod_pos fun j _ => (hπ j).1 (σ j)
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hm (a : S i) : ((productMass π (Function.update σ i a) : ℝ) : ℂ) =
      (c : ℂ) * (π i a : ℂ) := by
    rw [productMass_update]
    change ((π i a * c : ℝ) : ℂ) = (c : ℂ) * (π i a : ℂ)
    rw [Complex.ofReal_mul, mul_comm]
  simp_rw [hm]
  have hn : (∑ a, (π i a : ℂ)) = 1 := by exact_mod_cast (hπ i).2
  rw [← Finset.mul_sum, hn, mul_one]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, mul_div_cancel_left₀ _ hc']
  rfl

omit [Fintype ι] in
lemma average_re (π : (i : ι) → Weight (S i)) (i : ι)
    (f : Config S → ℂ) (σ : Config S) :
    (average (fun j a => (π j a : ℂ)) i f σ).re =
      average π i (fun τ => (f τ).re) σ := by
  simp [average, Complex.mul_re]

omit [Fintype ι] in
lemma average_im (π : (i : ι) → Weight (S i)) (i : ι)
    (f : Config S → ℂ) (σ : Config S) :
    (average (fun j a => (π j a : ℂ)) i f σ).im =
      average π i (fun τ => (f τ).im) σ := by
  simp [average, Complex.mul_im]

end AKLT.W.GAP016
