module
public import AKLT.Blueprint.Gap.NodesFinite
public import AKLT.Vendor.QICLean.Analysis.KernelSpectralGap
public import Mathlib.Analysis.Matrix.Spectrum

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ComplexConjugate Matrix
open AKLT.Defs AKLT.Blueprint.Gap

namespace AKLT.W.GAP023

local instance (α : Type) : DecidableEq α := Classical.decEq α

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- The reversible kernel conjugated by the square roots of the stationary weights. -/
def conjugatedKernel (p : Weight Ω) (K : Ω → Weight Ω) : Matrix Ω Ω ℂ :=
  fun i j => (Real.sqrt (p i) : ℂ) * (K i j : ℂ) / (Real.sqrt (p j) : ℂ)

def conjugatedGap (p : Weight Ω) (K : Ω → Weight Ω) : Matrix Ω Ω ℂ :=
  1 - conjugatedKernel p K

lemma conjugatedKernel_hermitian (p : Weight Ω) (K : Ω → Weight Ω)
    (hp : PositiveProbability p) (hrev : Reversible p K) :
    (conjugatedKernel p K).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  have hi : Real.sqrt (p i) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (hp.1 i))
  have hj : Real.sqrt (p j) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (hp.1 j))
  have hdb := hrev.2 i j
  have hsqi := Real.sq_sqrt (le_of_lt (hp.1 i))
  have hsqj := Real.sq_sqrt (le_of_lt (hp.1 j))
  change star (conjugatedKernel p K j i) = conjugatedKernel p K i j
  simp [conjugatedKernel]
  have hic : (Real.sqrt (p i) : ℂ) ≠ 0 := by exact_mod_cast hi
  have hjc : (Real.sqrt (p j) : ℂ) ≠ 0 := by exact_mod_cast hj
  have hdb' : Real.sqrt (p i) ^ 2 * K i j = Real.sqrt (p j) ^ 2 * K j i := by
    rw [hsqi, hsqj]
    exact hrev.2 i j
  apply (div_eq_div_iff hic hjc).2
  norm_cast
  nlinarith [hdb']


lemma conjugatedGap_hermitian (p : Weight Ω) (K : Ω → Weight Ω)
    (hp : PositiveProbability p) (hrev : Reversible p K) :
    (conjugatedGap p K).IsHermitian := by
  unfold conjugatedGap
  exact Matrix.IsHermitian.sub (Matrix.isHermitian_one) (conjugatedKernel_hermitian p K hp hrev)

/-- The complex action of a real kernel. -/
def kernelMeanC (K : Ω → Weight Ω) (f : Ω → ℂ) : Ω → ℂ :=
  fun i => ∑ j, (K i j : ℂ) * f j

lemma sqrtWeight_ne_zero (p : Weight Ω) (hp : PositiveProbability p) (i : Ω) :
    (Real.sqrt (p i) : ℂ) ≠ 0 := by
  exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (hp.1 i)))

lemma conjugatedKernel_mulVec_div (p : Weight Ω) (K : Ω → Weight Ω)
    (hp : PositiveProbability p) (v : Ω → ℂ) (i : Ω) :
    (conjugatedKernel p K *ᵥ v) i = (Real.sqrt (p i) : ℂ) *
      kernelMeanC K (fun j => v j / (Real.sqrt (p j) : ℂ)) i := by
  simp only [Matrix.mulVec, conjugatedKernel, kernelMeanC]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn := sqrtWeight_ne_zero p hp j
  field_simp [hjn]

lemma conjugatedKernel_mulVec_scaled (p : Weight Ω) (K : Ω → Weight Ω)
    (hp : PositiveProbability p) (f : Ω → ℂ) (i : Ω) :
    (conjugatedKernel p K *ᵥ (fun j => (Real.sqrt (p j) : ℂ) * f j)) i =
      (Real.sqrt (p i) : ℂ) * kernelMeanC K f i := by
  rw [conjugatedKernel_mulVec_div p K hp (fun j => (Real.sqrt (p j) : ℂ) * f j) i]
  apply congrArg (fun z : ℂ => (Real.sqrt (p i) : ℂ) * z)
  unfold kernelMeanC
  apply Finset.sum_congr rfl
  intro j hj
  have hjn := sqrtWeight_ne_zero p hp j
  field_simp [hjn]

lemma kernelMeanC_eigen_of_conjugated (p : Weight Ω) (K : Ω → Weight Ω)
    (hp : PositiveProbability p) (v : Ω → ℂ) (lam : ℂ)
    (h : conjugatedKernel p K *ᵥ v = lam • v) :
    kernelMeanC K (fun j => v j / (Real.sqrt (p j) : ℂ)) =
      lam • (fun j => v j / (Real.sqrt (p j) : ℂ)) := by
  funext i
  have hi := sqrtWeight_ne_zero p hp i
  change kernelMeanC K (fun j => v j / (Real.sqrt (p j) : ℂ)) i =
    lam * (v i / (Real.sqrt (p i) : ℂ))
  have hpoint := congrFun h i
  rw [conjugatedKernel_mulVec_div p K hp v i] at hpoint
  simp only [Pi.smul_apply, smul_eq_mul] at hpoint
  have hv : v i = (Real.sqrt (p i) : ℂ) * (v i / (Real.sqrt (p i) : ℂ)) := by
    field_simp [hi]
  rw [hv] at hpoint
  have hpoint' : (Real.sqrt (p i) : ℂ) *
      kernelMeanC K (fun j => v j / (Real.sqrt (p j) : ℂ)) i =
      (Real.sqrt (p i) : ℂ) *
        (lam * (v i / (Real.sqrt (p i) : ℂ))) := by
    calc
      _ = lam * ((Real.sqrt (p i) : ℂ) * (v i / (Real.sqrt (p i) : ℂ))) := hpoint
      _ = _ := by ring
  exact (mul_left_cancel₀ hi hpoint')

lemma kernelMeanC_eigen_of_gap_eigenvector (p : Weight Ω) (K : Ω → Weight Ω)
    (hp : PositiveProbability p) (v : Ω → ℂ) (e : ℝ)
    (h : conjugatedGap p K *ᵥ v = (e : ℂ) • v) :
    kernelMeanC K (fun j => v j / (Real.sqrt (p j) : ℂ)) =
      (1 - (e : ℂ)) • (fun j => v j / (Real.sqrt (p j) : ℂ)) := by
  have hsub : v - conjugatedKernel p K *ᵥ v = (e : ℂ) • v := by
    simpa [conjugatedGap, Matrix.sub_mulVec] using h
  have heig : conjugatedKernel p K *ᵥ v = (1 - (e : ℂ)) • v := by
    ext i
    have hi := congrFun hsub i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
    linear_combination -hi
  exact kernelMeanC_eigen_of_conjugated p K hp v (1 - (e : ℂ)) heig

lemma complexMean_kernel_eq (p : Weight Ω) (K : Ω → Weight Ω)
    (hp : PositiveProbability p) (hrev : Reversible p K) (f : Ω → ℂ) :
    complexMean p (kernelMeanC K f) = complexMean p f := by
  unfold complexMean kernelMeanC
  calc
    (∑ i, (p i : ℂ) * ∑ j, (K i j : ℂ) * f j) =
        ∑ i, ∑ j, ((p i : ℂ) * (K i j : ℂ)) * f j := by
          simp [Finset.mul_sum, mul_assoc]
    _ = ∑ j, ∑ i, ((p i : ℂ) * (K i j : ℂ)) * f j := by rw [Finset.sum_comm]
    _ = ∑ j, ∑ i, ((p j : ℂ) * (K j i : ℂ)) * f j := by
          apply Finset.sum_congr rfl
          intro j hj
          apply Finset.sum_congr rfl
          intro i hi
          have hdb : (p i : ℂ) * (K i j : ℂ) = (p j : ℂ) * (K j i : ℂ) := by
            exact_mod_cast hrev.2 i j
          rw [hdb]
    _ = ∑ j, (p j : ℂ) * f j := by
          apply Finset.sum_congr rfl
          intro j hj
          have hrow : (∑ i, (K j i : ℂ)) = 1 := by
            have := (hrev.1 j).2
            exact_mod_cast this
          rw [show (∑ i, ((p j : ℂ) * (K j i : ℂ)) * f j) =
              ((p j : ℂ) * f j) * ∑ i, (K j i : ℂ) by
                simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]]
          rw [hrow, mul_one]
    _ = ∑ i, (p i : ℂ) * f i := rfl

lemma complexMean_smul (p : Weight Ω) (a : ℂ) (f : Ω → ℂ) :
    complexMean p (fun i => a * f i) = a * complexMean p f := by
  unfold complexMean
  calc
    (∑ i, (p i : ℂ) * (a * f i)) = ∑ i, a * ((p i : ℂ) * f i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = a * ∑ i, (p i : ℂ) * f i := by rw [Finset.mul_sum]

lemma complexMean_re (p : Weight Ω) (f : Ω → ℂ) :
    (complexMean p f).re = expectation p (fun i => (f i).re) := by
  unfold complexMean expectation
  simp [map_sum, Complex.mul_re]

lemma complexMean_im (p : Weight Ω) (f : Ω → ℂ) :
    (complexMean p f).im = expectation p (fun i => (f i).im) := by
  unfold complexMean expectation
  simp [map_sum, Complex.mul_im]

lemma kernelMeanC_re (K : Ω → Weight Ω) (f : Ω → ℂ) :
    (fun i => (kernelMeanC K f i).re) = kernelMean K (fun j => (f j).re) := by
  funext i
  simp [kernelMeanC, kernelMean, expectation, map_sum, Complex.mul_re]

lemma kernelMeanC_im (K : Ω → Weight Ω) (f : Ω → ℂ) :
    (fun i => (kernelMeanC K f i).im) = kernelMean K (fun j => (f j).im) := by
  funext i
  simp [kernelMeanC, kernelMean, expectation, map_sum, Complex.mul_im]

lemma transformed_nonzero {p : Weight Ω} (hp : PositiveProbability p)
    {v : Ω → ℂ} (hv : v ≠ 0) :
    (fun j => v j / (Real.sqrt (p j) : ℂ)) ≠ 0 := by
  intro hzero
  apply hv
  funext j
  have hj := sqrtWeight_ne_zero p hp j
  have hz := congrFun hzero j
  field_simp [hj] at hz
  simpa using hz

lemma reversible_eigenvalue_lower_bound
    (p : Weight Ω) (K : Ω → Weight Ω) (hp : PositiveProbability p)
    (hrev : Reversible p K) (A c : ℝ) (hA : 0 < A) (hc : 0 < c) (hcA : c ≤ A)
    (heigen : ∀ (f : Ω → ℝ) (eigenvalue : ℝ), expectation p f = 0 →
      (∃ i, f i ≠ 0) → (∀ i, kernelMean K f i = eigenvalue * f i) →
      eigenvalue ≤ 1 - c / A)
    {v : Ω → ℂ} {e : ℝ}
    (hv : conjugatedGap p K *ᵥ v = (e : ℂ) • v) (hvne : v ≠ 0) (he : e ≠ 0) :
    c / A ≤ e := by
  let f : Ω → ℂ := fun j => v j / (Real.sqrt (p j) : ℂ)
  have hfne : f ≠ 0 := transformed_nonzero hp hvne
  have heig := kernelMeanC_eigen_of_gap_eigenvector p K hp v e hv
  have hmeanKernel := complexMean_kernel_eq p K hp hrev f
  have hmeanScale := complexMean_smul p (1 - (e : ℂ)) f
  have heig' : kernelMeanC K f = fun i => (1 - (e : ℂ)) * f i := by
    funext i
    have hi := congrFun heig i
    change kernelMeanC K f i = (1 - (e : ℂ)) * f i
    simpa only [Pi.smul_apply, smul_eq_mul] using hi
  have hmean0 : complexMean p f = 0 := by
    have hfixed : (1 - (e : ℂ)) * complexMean p f = complexMean p f := by
      calc
        (1 - (e : ℂ)) * complexMean p f = complexMean p (fun i => (1 - (e : ℂ)) * f i) := hmeanScale.symm
        _ = complexMean p (kernelMeanC K f) := by rw [← heig']
        _ = complexMean p f := hmeanKernel
    have hprod : ((1 - (e : ℂ)) - 1) * complexMean p f = 0 := by
      linear_combination hfixed
    have hcoef : ((1 - (e : ℂ)) - 1) ≠ 0 := by
      have heC : (e : ℂ) ≠ 0 := by exact_mod_cast he
      simpa using heC
    rcases mul_eq_zero.mp hprod with hzero | hzero
    · exact (hcoef hzero).elim
    · exact hzero
  have hmeanRe : expectation p (fun i => (f i).re) = 0 := by
    rw [← complexMean_re]
    exact congrArg Complex.re hmean0
  have hmeanIm : expectation p (fun i => (f i).im) = 0 := by
    rw [← complexMean_im]
    exact congrArg Complex.im hmean0
  have hnonzero : (fun i => (f i).re) ≠ 0 ∨ (fun i => (f i).im) ≠ 0 := by
    by_contra hh
    push_neg at hh
    apply hfne
    funext i
    exact Complex.ext (congrFun hh.1 i) (congrFun hh.2 i)
  have hbound : 1 - (e : ℝ) ≤ 1 - c / A := by
    rcases hnonzero with hre | him
    · apply heigen (fun i => (f i).re) (1 - e)
      · exact hmeanRe
      · exact Function.ne_iff.mp hre
      · intro i
        have h := congrFun heig i
        have hr := congrArg Complex.re h
        rw [← kernelMeanC_re K f]
        simpa [f, Complex.mul_re] using hr
    · apply heigen (fun i => (f i).im) (1 - e)
      · exact hmeanIm
      · exact Function.ne_iff.mp him
      · intro i
        have h := congrFun heig i
        have hi := congrArg Complex.im h
        rw [← kernelMeanC_im K f]
        simpa [f, Complex.mul_im] using hi
  linarith

lemma conjugatedGap_spectrum_lower_bound (p : Weight Ω) (K : Ω → Weight Ω)
    (hp : PositiveProbability p) (hrev : Reversible p K) (A c : ℝ)
    (hA : 0 < A) (hc : 0 < c) (hcA : c ≤ A)
    (heigen : ∀ (f : Ω → ℝ) (eigenvalue : ℝ), expectation p f = 0 →
      (∃ i, f i ≠ 0) → (∀ i, kernelMean K f i = eigenvalue * f i) →
      eigenvalue ≤ 1 - c / A) :
    ∀ e ∈ spectrum ℝ (conjugatedGap p K), e = 0 ∨ c / A ≤ e := by
  let hL := conjugatedGap_hermitian p K hp hrev
  intro e he
  rw [hL.spectrum_real_eq_range_eigenvalues] at he
  rcases he with ⟨i, rfl⟩
  by_cases hzero : hL.eigenvalues i = 0
  · exact Or.inl hzero
  · right
    let v : Ω → ℂ := ⇑(hL.eigenvectorBasis i)
    have hvne : v ≠ 0 := by
      intro hvz
      have hvec : hL.eigenvectorBasis i = 0 := by
        apply WithLp.ofLp_injective 2
        exact hvz
      have hnorm := hL.eigenvectorBasis.orthonormal.norm_eq_one i
      rw [hvec, norm_zero] at hnorm
      norm_num at hnorm
    have heig : conjugatedGap p K *ᵥ v = (hL.eigenvalues i : ℂ) • v := by
      simpa [v] using hL.mulVec_eigenvectorBasis i
    exact reversible_eigenvalue_lower_bound p K hp hrev A c hA hc hcA heigen
      heig hvne hzero

lemma kernelMeanC_const (K : Ω → Weight Ω) (hK : ∀ i, Probability (K i))
    (a : ℂ) (i : Ω) : kernelMeanC K (fun _ => a) i = a := by
  unfold kernelMeanC
  have hrow : (∑ j, (K i j : ℂ)) = 1 := by exact_mod_cast (hK i).2
  rw [← Finset.sum_mul, hrow, one_mul]

lemma kernelMeanC_sub_const (K : Ω → Weight Ω) (hK : ∀ i, Probability (K i))
    (f : Ω → ℂ) (a : ℂ) (i : Ω) :
    kernelMeanC K (fun j => f j - a) i = kernelMeanC K f i - a := by
  change (∑ j, (K i j : ℂ) * (f j - a)) = (∑ j, (K i j : ℂ) * f j) - a
  calc
    (∑ j, (K i j : ℂ) * (f j - a)) =
        ∑ j, ((K i j : ℂ) * f j - (K i j : ℂ) * a) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = (∑ j, (K i j : ℂ) * f j) - (∑ j, (K i j : ℂ) * a) := by
          rw [Finset.sum_sub_distrib]
    _ = (∑ j, (K i j : ℂ) * f j) - a := by
          rw [← Finset.sum_mul, show (∑ j, (K i j : ℂ)) = 1 by exact_mod_cast (hK i).2,
            one_mul]

lemma complexMean_sub_const (p : Weight Ω) (hp : PositiveProbability p)
    (f : Ω → ℂ) (a : ℂ) :
    complexMean p (fun i => f i - a) = complexMean p f - a := by
  change (∑ i, (p i : ℂ) * (f i - a)) = (∑ i, (p i : ℂ) * f i) - a
  calc
    (∑ i, (p i : ℂ) * (f i - a)) =
        ∑ i, ((p i : ℂ) * f i - (p i : ℂ) * a) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = (∑ i, (p i : ℂ) * f i) - (∑ i, (p i : ℂ) * a) := by
          rw [Finset.sum_sub_distrib]
    _ = (∑ i, (p i : ℂ) * f i) - a := by
          rw [← Finset.sum_mul, show (∑ i, (p i : ℂ)) = 1 by exact_mod_cast hp.2,
            one_mul]

lemma mean_zero_fixed_is_zero (p : Weight Ω) (K : Ω → Weight Ω)
    (hp : PositiveProbability p) (hrev : Reversible p K) (A c : ℝ)
    (hA : 0 < A) (hc : 0 < c)
    (heigen : ∀ (f : Ω → ℝ) (eigenvalue : ℝ), expectation p f = 0 →
      (∃ i, f i ≠ 0) → (∀ i, kernelMean K f i = eigenvalue * f i) →
      eigenvalue ≤ 1 - c / A)
    (f : Ω → ℂ) (hmean : complexMean p f = 0)
    (hfix : kernelMeanC K f = f) : f = 0 := by
  have hmeanRe : expectation p (fun i => (f i).re) = 0 := by
    rw [← complexMean_re]
    exact congrArg Complex.re hmean
  have hmeanIm : expectation p (fun i => (f i).im) = 0 := by
    rw [← complexMean_im]
    exact congrArg Complex.im hmean
  have hre : (fun i => (f i).re) = 0 := by
    by_contra hne
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    have heq : ∀ j, kernelMean K (fun k => (f k).re) j = 1 * (f j).re := by
      intro j
      have h := congrArg Complex.re (congrFun hfix j)
      have heq := (congrFun (kernelMeanC_re K f) j).symm.trans h
      simpa using heq
    have hbound := heigen (fun i => (f i).re) 1 hmeanRe ⟨i, hi⟩ heq
    have hpos : 0 < c / A := div_pos hc hA
    linarith
  have him : (fun i => (f i).im) = 0 := by
    by_contra hne
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    have heq : ∀ j, kernelMean K (fun k => (f k).im) j = 1 * (f j).im := by
      intro j
      have h := congrArg Complex.im (congrFun hfix j)
      have heq := (congrFun (kernelMeanC_im K f) j).symm.trans h
      simpa using heq
    have hbound := heigen (fun i => (f i).im) 1 hmeanIm ⟨i, hi⟩ heq
    have hpos : 0 < c / A := div_pos hc hA
    linarith
  funext i
  exact Complex.ext (congrFun hre i) (congrFun him i)

lemma kernel_fixed_is_constant (p : Weight Ω) (K : Ω → Weight Ω)
    (hp : PositiveProbability p) (hrev : Reversible p K) (A c : ℝ)
    (hA : 0 < A) (hc : 0 < c)
    (heigen : ∀ (f : Ω → ℝ) (eigenvalue : ℝ), expectation p f = 0 →
      (∃ i, f i ≠ 0) → (∀ i, kernelMean K f i = eigenvalue * f i) →
      eigenvalue ≤ 1 - c / A)
    (f : Ω → ℂ) (hfix : kernelMeanC K f = f) :
    f = fun _ => complexMean p f := by
  let m := complexMean p f
  have hmean0 : complexMean p (fun i => f i - m) = 0 := by
    rw [complexMean_sub_const p hp f m]
    simp [m]
  have hfix0 : kernelMeanC K (fun i => f i - m) = fun i => f i - m := by
    funext i
    rw [kernelMeanC_sub_const K hrev.1 f m, hfix]
  have hzero := mean_zero_fixed_is_zero p K hp hrev A c hA hc heigen
    (fun i => f i - m) hmean0 hfix0
  funext i
  have := congrFun hzero i
  dsimp [m] at this
  exact sub_eq_zero.mp this

lemma complexMean_sub (p : Weight Ω) (f g : Ω → ℂ) :
    complexMean p (fun i => f i - g i) = complexMean p f - complexMean p g := by
  unfold complexMean
  simp only [mul_sub, Finset.sum_sub_distrib]

lemma weightedInner_center_left (p : Weight Ω) (f h : Ω → ℂ) (m : ℂ) :
    weightedInner p f h = weightedInner p (fun i => f i - m) h +
      star m * complexMean p h := by
  unfold weightedInner complexMean
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [star_sub]
  ring

lemma centered_scaled_norm (p : Weight Ω) (hp : PositiveProbability p)
    (f : Ω → ℂ) :
    ‖WithLp.toLp 2 (fun i => (Real.sqrt (p i) : ℂ) *
      (f i - complexMean p f))‖ ^ 2 = variance p f := by
  rw [EuclideanSpace.norm_sq_eq]
  change (∑ i, ‖(Real.sqrt (p i) : ℂ) * (f i - complexMean p f)‖ ^ 2) = _
  unfold variance
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Complex.normSq_eq_norm_sq]
  have hq : Complex.normSq (Real.sqrt (p i) : ℂ) = p i := by
    rw [Complex.normSq_ofReal, ← pow_two, Real.sq_sqrt (le_of_lt (hp.1 i))]
  rw [Complex.normSq_mul, hq]

lemma conjugatedGap_mulVec_scaled_centered (p : Weight Ω) (K : Ω → Weight Ω)
    (hp : PositiveProbability p) (f : Ω → ℂ) :
    conjugatedGap p K *ᵥ (fun i => (Real.sqrt (p i) : ℂ) * f i) =
      (fun i => (Real.sqrt (p i) : ℂ) * (f i - kernelMeanC K f i)) := by
  funext i
  change ((1 - conjugatedKernel p K) *ᵥ
    (fun j => (Real.sqrt (p j) : ℂ) * f j)) i = _
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  simp only [Pi.sub_apply]
  rw [conjugatedKernel_mulVec_scaled p K hp f i]
  ring

lemma weightedEnergy_center (p : Weight Ω) (K : Ω → Weight Ω)
    (hp : PositiveProbability p) (hrev : Reversible p K) (f : Ω → ℂ) :
    weightedInner p f (fun i => f i - kernelMeanC K f i) =
      weightedInner p (fun i => f i - complexMean p f)
        (fun i => (f i - complexMean p f) - kernelMeanC K (fun j => f j - complexMean p f) i) := by
  let m := complexMean p f
  let g : Ω → ℂ := fun i => f i - m
  have hK : kernelMeanC K g = fun i => kernelMeanC K f i - m := by
    funext i
    exact kernelMeanC_sub_const K hrev.1 f m i
  have hdiff : (fun i => g i - kernelMeanC K g i) =
      (fun i => f i - kernelMeanC K f i) := by
    funext i
    rw [hK]
    dsimp [g]
    ring
  have hmeanDiff : complexMean p (fun i => f i - kernelMeanC K f i) = 0 := by
    rw [complexMean_sub]
    rw [complexMean_kernel_eq p K hp hrev f]
    ring
  have hcenter := weightedInner_center_left p f
      (fun i => f i - kernelMeanC K f i) m
  rw [hmeanDiff, mul_zero, add_zero] at hcenter
  rw [hcenter]
  dsimp [g, m] at hdiff ⊢
  rw [hdiff]

/-- Main closed leaf: reversible diagonalization yields the Poincare inequality. -/
theorem main : AKLT.Blueprint.Gap.ReversibleEigenvalueGapStatement := by
  classical
  intro ι hι hιeq S hS hSN p K hp hrev A c hA hc hcA heigen f
  let g : Config S → ℂ := fun σ => f σ - complexMean p f
  let u : Config S → ℂ := fun σ => (Real.sqrt (p σ) : ℂ) * g σ
  let x : EuclideanSpace ℂ (Config S) := WithLp.toLp 2 u
  let L := conjugatedGap p K
  have hL : L.IsHermitian := conjugatedGap_hermitian p K hp hrev
  have hspec0 := conjugatedGap_spectrum_lower_bound p K hp hrev A c hA hc hcA heigen
  have hspec : ∀ e ∈ spectrum ℝ L, e = 0 ∨ c / A ≤ e := by
    intro e he
    apply hspec0 e
    simpa [L] using he
  have hmeanG : complexMean p g = 0 := by
    dsimp [g]
    rw [complexMean_sub_const p hp]
    ring
  have hnorm : ‖x‖ ^ 2 = variance p f := by
    change ‖WithLp.toLp 2 u‖ ^ 2 = variance p f
    simpa [u, g] using centered_scaled_norm p hp f
  have horth : ∀ z : EuclideanSpace ℂ (Config S),
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Config S) L z = 0 → inner ℂ z x = 0 := by
    intro z hz
    let v : Config S → ℂ := WithLp.ofLp z
    have hzmul : L *ᵥ v = 0 := by
      have hz' := congrArg (WithLp.ofLp (p := 2)) hz
      simpa [L, v, Matrix.ofLp_toEuclideanCLM] using hz'
    have hsub : v - conjugatedKernel p K *ᵥ v = 0 := by
      change ((1 - conjugatedKernel p K) *ᵥ v) = 0 at hzmul
      simpa only [Matrix.sub_mulVec, Matrix.one_mulVec] using hzmul
    have hfixV : conjugatedKernel p K *ᵥ v = v := by
      funext σ
      exact (sub_eq_zero.mp (congrFun hsub σ)).symm
    let fv : Config S → ℂ := fun σ => v σ / (Real.sqrt (p σ) : ℂ)
    have hfix : kernelMeanC K fv = fv := by
      have hh := kernelMeanC_eigen_of_conjugated p K hp v 1 (by simpa using hfixV)
      simpa [fv] using hh
    have hconst := kernel_fixed_is_constant p K hp hrev A c hA hc heigen fv hfix
    have hvconst : v = fun σ => (Real.sqrt (p σ) : ℂ) * complexMean p fv := by
      funext σ
      have hq := sqrtWeight_ne_zero p hp σ
      have hdiv : v σ = (Real.sqrt (p σ) : ℂ) * fv σ := by
        dsimp [fv]
        field_simp [hq]
      rw [hdiv, congrFun hconst σ]
    have hzrep : z = WithLp.toLp 2 v := (WithLp.toLp_ofLp (p := 2) z).symm
    rw [hzrep, EuclideanSpace.inner_toLp_toLp]
    change (∑ σ, u σ * star (v σ)) = 0
    have hsum : (∑ σ, u σ * star (v σ)) =
        star (complexMean p fv) * ∑ σ, (p σ : ℂ) * g σ := by
      unfold u
      calc
        (∑ σ, (Real.sqrt (p σ) : ℂ) * g σ * star (v σ)) =
          ∑ σ, (Real.sqrt (p σ) : ℂ) * g σ *
            star ((Real.sqrt (p σ) : ℂ) * complexMean p fv) := by
              apply Finset.sum_congr rfl
              intro σ hσ
              rw [congrFun hvconst σ]
        _ = ∑ σ, star (complexMean p fv) * ((p σ : ℂ) * g σ) := by
            apply Finset.sum_congr rfl
            intro σ hσ
            have hq : (Real.sqrt (p σ) : ℂ) * (Real.sqrt (p σ) : ℂ) = (p σ : ℂ) := by
              have hqR : Real.sqrt (p σ) * Real.sqrt (p σ) = p σ := by
                simpa [pow_two] using Real.sq_sqrt (le_of_lt (hp.1 σ))
              exact_mod_cast hqR
            have hqstar : star (Real.sqrt (p σ) : ℂ) = (Real.sqrt (p σ) : ℂ) := by
              change (starRingEnd ℂ) (Real.sqrt (p σ) : ℂ) = _
              rw [Complex.conj_ofReal]
            rw [star_mul, hqstar]
            calc
              _ = star (complexMean p fv) *
                    ((Real.sqrt (p σ) : ℂ) * (Real.sqrt (p σ) : ℂ) * g σ) := by ring
              _ = _ := by rw [hq]
        _ = star (complexMean p fv) * ∑ σ, (p σ : ℂ) * g σ := by rw [Finset.mul_sum]
    rw [hsum]
    have hsum0 : (∑ σ, (p σ : ℂ) * g σ) = 0 := by
      simpa [complexMean] using hmeanG
    rw [hsum0]
    simp
  have hgap := AKLT.Vendor.QICLean.Matrix.IsHermitian.mul_norm_sq_le_re_inner_of_spectral_gap
    hL hspec x horth
  have henergy : (inner ℂ x (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Config S) L x)).re =
      (weightedInner p f (fun σ => f σ - kernelMeanC K f σ)).re := by
    change (inner ℂ (WithLp.toLp 2 u)
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Config S) L (WithLp.toLp 2 u))).re = _
    rw [Matrix.toEuclideanCLM_toLp, EuclideanSpace.inner_toLp_toLp]
    change (∑ σ, (L *ᵥ u) σ * star (u σ)).re = _
    rw [show L *ᵥ u = fun σ => (Real.sqrt (p σ) : ℂ) *
      (g σ - kernelMeanC K g σ) by
        dsimp [L, u, g]
        exact conjugatedGap_mulVec_scaled_centered p K hp (fun σ => f σ - complexMean p f)]
    have hcomplex : ∑ σ, ((Real.sqrt (p σ) : ℂ) *
        (g σ - kernelMeanC K g σ)) *
        star ((Real.sqrt (p σ) : ℂ) * g σ) =
        weightedInner p g (fun σ => g σ - kernelMeanC K g σ) := by
      unfold weightedInner
      apply Finset.sum_congr rfl
      intro σ hσ
      have hq : (Real.sqrt (p σ) : ℂ) * (Real.sqrt (p σ) : ℂ) = (p σ : ℂ) := by
        have hqR : Real.sqrt (p σ) * Real.sqrt (p σ) = p σ := by
          simpa [pow_two] using Real.sq_sqrt (le_of_lt (hp.1 σ))
        exact_mod_cast hqR
      have hqstar : star (Real.sqrt (p σ) : ℂ) = (Real.sqrt (p σ) : ℂ) := by
        change (starRingEnd ℂ) (Real.sqrt (p σ) : ℂ) = _
        rw [Complex.conj_ofReal]
      rw [star_mul, hqstar]
      calc
        _ = ((Real.sqrt (p σ) : ℂ) * (Real.sqrt (p σ) : ℂ)) *
              star (g σ) * (g σ - kernelMeanC K g σ) := by ring
        _ = _ := by rw [hq]
    have hcenter := weightedEnergy_center p K hp hrev f
    rw [hcomplex, hcenter]
  calc
    c * variance p f = A * ((c / A) * ‖x‖ ^ 2) := by
      rw [hnorm]
      field_simp [ne_of_gt hA]
    _ ≤ A * (inner ℂ x (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Config S) L x)).re :=
      mul_le_mul_of_nonneg_left hgap (le_of_lt hA)
    _ = kernelForm p K A f := by
      unfold kernelForm
      simpa [kernelMeanC] using congrArg (fun r : ℝ => A * r) henergy

end AKLT.W.GAP023
