import AKLT.W.GAP016.RealTensorization
import AKLT.W.GAP016.Conditioning

/-! Product tensorization for the finite heat-bath Dirichlet form.
The real inequality is proved by finite orthogonal projection induction;
the complex inequality is its sum on the real and imaginary components. -/

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Gap

namespace AKLT.W.GAP016

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {S : ι → Type} [∀ i, Fintype (S i)]

lemma variance_re_im (π : (i : ι) → Weight (S i)) (f : Config S → ℂ) :
    variance (productMass π) f =
      realVariance π (fun σ => (f σ).re) + realVariance π (fun σ => (f σ).im) := by
  have hre : (complexMean (productMass π) f).re = realMean π (fun σ => (f σ).re) := by
    simp [complexMean, realMean, Complex.mul_re]
  have him : (complexMean (productMass π) f).im = realMean π (fun σ => (f σ).im) := by
    simp [complexMean, realMean, Complex.mul_im]
  unfold variance realVariance squareMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hre, him]
  ring

lemma blockDirichlet_re_im (π : (i : ι) → Weight (S i))
    (hπ : ∀ i, PositiveProbability (π i)) (i : ι) (f : Config S → ℂ) :
    blockDirichlet (productMass π) {i} f =
      siteEnergy π i (fun σ => (f σ).re) + siteEnergy π i (fun σ => (f σ).im) := by
  unfold blockDirichlet siteEnergy squareMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  rw [conditionalExpectation_product_singleton π hπ i f σ]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, average_re, average_im]
  ring

/-- A positive normalized finite product has heat-bath Poincare constant at least one,
including the product over no sites. -/
theorem main : AKLT.Blueprint.Gap.ProductTensorizationStatement := by
  intro ι _ _ S _ _ π hπ f
  change 1 * variance (productMass π) f ≤ dirichlet (productMass π) f
  rw [one_mul, variance_re_im]
  unfold dirichlet
  simp_rw [blockDirichlet_re_im π hπ]
  rw [Finset.sum_add_distrib]
  exact add_le_add (real_tensorization π hπ _) (real_tensorization π hπ _)

#print axioms main

end AKLT.W.GAP016
