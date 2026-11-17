module
public import AKLT.W.GAP016.Product

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Gap

namespace AKLT.W.GAP016

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {S : ι → Type} [∀ i, Fintype (S i)]

def squareMass (π : (i : ι) → Weight (S i)) (f : Config S → ℝ) : ℝ :=
  ∑ σ, productMass π σ * (f σ)^2

def realMean (π : (i : ι) → Weight (S i)) (f : Config S → ℝ) : ℝ :=
  ∑ σ, productMass π σ * f σ

def realVariance (π : (i : ι) → Weight (S i)) (f : Config S → ℝ) : ℝ :=
  squareMass π (fun σ => f σ - realMean π f)

def siteEnergy (π : (i : ι) → Weight (S i)) (i : ι) (f : Config S → ℝ) : ℝ :=
  squareMass π (fun σ => f σ - average π i f σ)

lemma squareMass_nonneg (π : (i : ι) → Weight (S i))
    (hπ : ∀ i, PositiveProbability (π i)) (f : Config S → ℝ) :
    0 ≤ squareMass π f := by
  exact Finset.sum_nonneg fun σ _ =>
    mul_nonneg ((productLaw_positiveProbability π hπ).1 σ).le (sq_nonneg _)

omit [Fintype ι] in
lemma average_mul_of_invariant (π : (i : ι) → Weight (S i)) (i : ι)
    (f g : Config S → ℝ)
    (hg : ∀ σ a, g (Function.update σ i a) = g σ) :
    average π i (fun σ => f σ * g σ) =
      (fun σ => average π i f σ * g σ) := by
  funext σ
  simp only [average, hg, ← mul_assoc, ← Finset.sum_mul]

/-- The coordinate average is an orthogonal projection for product mass. -/
lemma average_pythagoras (π : (i : ι) → Weight (S i))
    (hnorm : ∀ i, ∑ a, π i a = 1) (i : ι) (f : Config S → ℝ) :
    siteEnergy π i f = squareMass π f - squareMass π (average π i f) := by
  have hc : (∑ σ, productMass π σ * (f σ * average π i f σ)) =
      squareMass π (average π i f) := by
    have h := average_preserves_sum π hnorm i
      (fun σ => f σ * average π i f σ)
    rw [average_mul_of_invariant π i f (average π i f) (average_update π i f)] at h
    simpa only [squareMass, pow_two] using h.symm
  simp only [squareMass] at hc
  unfold siteEnergy squareMass
  calc
    (∑ σ, productMass π σ * (f σ - average π i f σ)^2) =
        (∑ σ, productMass π σ * (f σ)^2) +
          (∑ σ, productMass π σ * (average π i f σ)^2) -
          2 * ∑ σ, productMass π σ * (f σ * average π i f σ) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro σ _
      ring
    _ = _ := by rw [hc]; ring

lemma average_contracts (π : (i : ι) → Weight (S i))
    (hπ : ∀ i, PositiveProbability (π i)) (i : ι) (f : Config S → ℝ) :
    squareMass π (average π i f) ≤ squareMass π f := by
  have h := squareMass_nonneg π hπ (fun σ => f σ - average π i f σ)
  change 0 ≤ siteEnergy π i f at h
  rw [average_pythagoras π (fun i => (hπ i).2)] at h
  linarith

lemma realMean_average (π : (i : ι) → Weight (S i))
    (hnorm : ∀ i, ∑ a, π i a = 1) (i : ι) (f : Config S → ℝ) :
    realMean π (average π i f) = realMean π f :=
  average_preserves_sum π hnorm i f

lemma realVariance_eq (π : (i : ι) → Weight (S i))
    (hπ : ∀ i, PositiveProbability (π i)) (f : Config S → ℝ) :
    realVariance π f = squareMass π f - (realMean π f)^2 := by
  have hn := (productLaw_positiveProbability π hπ).2
  unfold realVariance squareMass
  calc
    (∑ σ, productMass π σ * (f σ - realMean π f)^2) =
      (∑ σ, productMass π σ * (f σ)^2) -
        2 * (realMean π f) * (∑ σ, productMass π σ * f σ) +
        (∑ σ, productMass π σ) * (realMean π f)^2 := by
      rw [Finset.mul_sum, Finset.sum_mul,
        ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro σ _
      ring
    _ = _ := by rw [hn]; unfold realMean; ring

lemma realVariance_decomposition (π : (i : ι) → Weight (S i))
    (hπ : ∀ i, PositiveProbability (π i)) (i : ι) (f : Config S → ℝ) :
    realVariance π f = siteEnergy π i f + realVariance π (average π i f) := by
  rw [realVariance_eq π hπ, realVariance_eq π hπ,
    average_pythagoras π (fun i => (hπ i).2),
    realMean_average π (fun i => (hπ i).2)]
  ring

lemma siteEnergy_average_le (π : (i : ι) → Weight (S i))
    (hπ : ∀ i, PositiveProbability (π i)) (i j : ι) (f : Config S → ℝ) :
    siteEnergy π j (average π i f) ≤ siteEnergy π j f := by
  unfold siteEnergy
  have hf : (fun σ => average π i f σ - average π j (average π i f) σ) =
      average π i (fun σ => f σ - average π j f σ) := by
    rw [average_sub, average_commute π i j f]
  rw [hf]
  exact average_contracts π hπ i _

/-- Finite tensorization, with the coordinates on which the function depends explicit. -/
lemma real_tensorization_on (π : (i : ι) → Weight (S i))
    (hπ : ∀ i, PositiveProbability (π i)) (U : Finset ι) :
    ∀ f : Config S → ℝ,
      (∀ σ τ, (∀ i ∈ U, σ i = τ i) → f σ = f τ) →
      realVariance π f ≤ ∑ i ∈ U, siteEnergy π i f := by
  classical
  induction U using Finset.induction_on with
  | empty =>
    intro f hf
    have hm (σ : Config S) : realMean π f = f σ := by
      unfold realMean
      simp_rw [hf _ σ (by simp)]
      rw [← Finset.sum_mul, (productLaw_positiveProbability π hπ).2, one_mul]
    have hz : realVariance π f = 0 := by
      unfold realVariance squareMass
      apply Finset.sum_eq_zero
      intro σ _
      rw [hm σ]
      simp
    simp [hz]
  | @insert i U hi ih =>
    intro f hf
    have hdep : ∀ σ τ, (∀ j ∈ U, σ j = τ j) →
        average π i f σ = average π i f τ := by
      intro σ τ hστ
      unfold average
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      apply hf
      intro j hj
      by_cases hji : j = i
      · subst j
        simp
      · simp only [Function.update_of_ne hji]
        exact hστ j ((Finset.mem_insert.mp hj).resolve_left hji)
    have hind := ih (average π i f) hdep
    have hcon : (∑ j ∈ U, siteEnergy π j (average π i f)) ≤
        ∑ j ∈ U, siteEnergy π j f := by
      exact Finset.sum_le_sum fun j _ => siteEnergy_average_le π hπ i j f
    rw [Finset.sum_insert hi, realVariance_decomposition π hπ i f]
    linarith

theorem real_tensorization (π : (i : ι) → Weight (S i))
    (hπ : ∀ i, PositiveProbability (π i)) (f : Config S → ℝ) :
    realVariance π f ≤ ∑ i, siteEnergy π i f := by
  apply real_tensorization_on π hπ Finset.univ f
  intro σ τ h
  exact congrArg f (funext fun i => h i (Finset.mem_univ i))

end AKLT.W.GAP016
