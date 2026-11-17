module
public import AKLT.W.GAP014.FiniteVariance

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Gap
attribute [local instance] Classical.propDecidable
namespace AKLT.W.GAP014
set_option maxHeartbeats 800000

section Product
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
  [∀ i, Fintype (S i)]

def productWeight (π : (i : ι) → Weight (S i)) : Weight (Config S) :=
  fun σ => ∏ i, π i (σ i)

lemma productWeight_probability (π : (i : ι) → Weight (S i))
    (hπ : ∀ i, PositiveProbability (π i)) : PositiveProbability (productWeight π) := by
  constructor
  · intro σ
    exact Finset.prod_pos fun i _ => (hπ i).1 (σ i)
  · unfold productWeight
    rw [← Fintype.prod_sum]
    simp only [fun i => (hπ i).2, Finset.prod_const_one]

private lemma sum_single_fibre {R : Type} [AddCommMonoid R] (i : ι) (σ : Config S)
    (g : Config S → R) :
    (∑ τ, if AgreeOutside {i} σ τ then g τ else 0) =
      ∑ a, g (Function.update σ i a) := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun τ _ => τ i)
  · intro τ _
    exact Finset.mem_univ _
  · intro τ hτ ρ hρ he
    have ht := (Finset.mem_filter.mp hτ).2
    have hr := (Finset.mem_filter.mp hρ).2
    funext j
    by_cases hj : j = i
    · subst j
      exact he
    · exact (ht j (by simpa using hj)).symm.trans (hr j (by simpa using hj))
  · intro a _
    refine ⟨Function.update σ i a, ?_, by simp⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro j hj
    have hji : j ≠ i := by simpa using hj
    simp [Function.update_of_ne hji]
  · intro τ hτ
    congr 1
    have ht := (Finset.mem_filter.mp hτ).2
    funext j
    by_cases hj : j = i
    · subst j
      simp
    · simpa [Function.update_of_ne hj] using (ht j (by simpa using hj)).symm

omit [∀ i, Fintype (S i)] in
private lemma productWeight_update (π : (i : ι) → Weight (S i)) (i : ι)
    (σ : Config S) (a : S i) :
    productWeight π (Function.update σ i a) =
      π i a * ∏ j ∈ Finset.univ.erase i, π j (σ j) := by
  unfold productWeight
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

private def coordinateAverage (π : (i : ι) → Weight (S i)) (i : ι)
    (f : Config S → ℂ) : Config S → ℂ :=
  fun σ => ∑ a, (π i a : ℂ) * f (Function.update σ i a)

private lemma ce_product (π : (i : ι) → Weight (S i))
    (hπ : ∀ i, PositiveProbability (π i)) (i : ι) (f : Config S → ℂ) :
    conditionalExpectation (productWeight π) {i} f = coordinateAverage π i f := by
  classical
  funext σ
  let C := ∏ j ∈ Finset.univ.erase i, π j (σ j)
  have hC : C ≠ 0 := (Finset.prod_pos fun j _ => (hπ j).1 (σ j)).ne'
  have hsum : (∑ a, (π i a : ℂ)) = 1 := by
    rw [← Complex.ofReal_sum, (hπ i).2, Complex.ofReal_one]
  unfold conditionalExpectation
  rw [sum_single_fibre, sum_single_fibre]
  simp_rw [productWeight_update, Complex.ofReal_mul]
  change (∑ a, ((π i a : ℂ) * (C : ℂ)) * f (Function.update σ i a)) /
    (∑ a, (π i a : ℂ) * (C : ℂ)) = coordinateAverage π i f σ
  rw [← Finset.sum_mul, hsum, one_mul]
  have hn : (∑ a, ((π i a : ℂ) * (C : ℂ)) * f (Function.update σ i a)) =
      coordinateAverage π i f σ * (C : ℂ) := by
    unfold coordinateAverage
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hn, mul_div_cancel_right₀ _ (Complex.ofReal_ne_zero.mpr hC)]

omit [Fintype ι] in
private lemma coordinateAverage_commute (π : (i : ι) → Weight (S i))
    {i j : ι} (hij : i ≠ j) (f : Config S → ℂ) :
    coordinateAverage π i (coordinateAverage π j f) =
      coordinateAverage π j (coordinateAverage π i f) := by
  funext σ
  unfold coordinateAverage
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  rw [Function.update_comm hij]
  ring

private lemma product_ce_commute (π : (i : ι) → Weight (S i))
    (hπ : ∀ i, PositiveProbability (π i)) {i j : ι} (hij : i ≠ j)
    (f : Config S → ℂ) :
    conditionalExpectation (productWeight π) {i}
      (conditionalExpectation (productWeight π) {j} f) =
    conditionalExpectation (productWeight π) {j}
      (conditionalExpectation (productWeight π) {i} f) := by
  simp_rw [ce_product π hπ]
  exact coordinateAverage_commute π hij f

private lemma product_ce_energy_le (π : (i : ι) → Weight (S i))
    (hπ : ∀ i, PositiveProbability (π i)) {i j : ι} (hij : i ≠ j)
    (f : Config S → ℂ) :
    blockDirichlet (productWeight π) {j}
      (conditionalExpectation (productWeight π) {i} f) ≤
    blockDirichlet (productWeight π) {j} f := by
  let q := productWeight π
  have he : (fun σ => conditionalExpectation q {i} f σ -
      conditionalExpectation q {j} (conditionalExpectation q {i} f) σ) =
      conditionalExpectation q {i} (fun σ => f σ - conditionalExpectation q {j} f σ) := by
    rw [ce_sub, product_ce_commute π hπ hij]
  calc
    _ = ∑ σ, q σ * Complex.normSq (conditionalExpectation q {i}
        (fun τ => f τ - conditionalExpectation q {j} f τ) σ) := by
      apply Finset.sum_congr rfl
      intro σ _
      exact congrArg (fun z : ℂ => q σ * Complex.normSq z) (congrFun he σ)
    _ ≤ _ := ce_energy_le q (productWeight_probability π hπ).1 {i} _

private lemma product_ce_depends (π : (i : ι) → Weight (S i))
    (hπ : ∀ i, PositiveProbability (π i)) (i : ι) (s : Finset ι)
    (f : Config S → ℂ)
    (hf : ∀ σ τ, AgreeOn (insert i s) σ τ → f σ = f τ) :
    ∀ σ τ, AgreeOn s σ τ →
      conditionalExpectation (productWeight π) {i} f σ =
      conditionalExpectation (productWeight π) {i} f τ := by
  intro σ τ hστ
  rw [ce_product π hπ]
  unfold coordinateAverage
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  apply hf
  intro j hj
  by_cases hji : j = i
  · subst j
    simp
  · have hj' : j ∈ s := (Finset.mem_insert.mp hj).resolve_left hji
    simpa only [Function.update_of_ne hji] using hστ j hj'

/-- Rate-one tensorization of a finite positive product, including zero sites. -/
theorem product_gap (π : (i : ι) → Weight (S i))
    (hπ : ∀ i, PositiveProbability (π i)) : PoincareLower (productWeight π) 1 := by
  classical
  let q := productWeight π
  have hq := productWeight_probability π hπ
  have aux (s : Finset ι) : ∀ f : Config S → ℂ,
      (∀ σ τ, AgreeOn s σ τ → f σ = f τ) →
      variance q f ≤ ∑ i ∈ s, blockDirichlet q {i} f := by
    induction s using Finset.induction with
    | empty =>
      intro f hf
      have hconst (σ τ : Config S) : f σ = f τ := hf σ τ (by simp [AgreeOn])
      have hmean (σ : Config S) : complexMean q f = f σ := by
        unfold complexMean
        calc
          _ = ∑ τ, (q τ : ℂ) * f σ := by
            apply Finset.sum_congr rfl
            intro τ _
            rw [hconst τ σ]
          _ = (∑ τ, (q τ : ℂ)) * f σ := (Finset.sum_mul ..).symm
          _ = f σ := by rw [← Complex.ofReal_sum, hq.2]; simp
      have hv : variance q f = 0 := by
        unfold variance
        apply Finset.sum_eq_zero
        intro σ _
        rw [hmean σ]
        simp
      simp [hv]
    | @insert i s hi ih =>
      intro f hf
      have hdep := product_ce_depends π hπ i s f hf
      have hv := ih (conditionalExpectation q {i} f) hdep
      have hc : (∑ j ∈ s, blockDirichlet q {j} (conditionalExpectation q {i} f)) ≤
          ∑ j ∈ s, blockDirichlet q {j} f := by
        apply Finset.sum_le_sum
        intro j hj
        exact product_ce_energy_le π hπ (i := i) (j := j) (by rintro rfl; exact hi hj) f
      rw [ce_variance_identity q hq.1 {i} f, Finset.sum_insert hi]
      exact add_le_add (le_refl _) (hv.trans hc)
  intro f
  simp only [one_mul]
  apply aux Finset.univ f
  intro σ τ hστ
  exact congrArg f (funext fun i => hστ i (Finset.mem_univ i))

end Product
end AKLT.W.GAP014
