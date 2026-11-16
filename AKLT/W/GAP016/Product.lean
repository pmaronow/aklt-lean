import AKLT.Blueprint.Gap.NodesFinite

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Gap

namespace AKLT.W.GAP016

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {S : ι → Type} [∀ i, Fintype (S i)]

/-- Product mass, also used for intermediate finite-sum identities. -/
def productMass {R : Type*} [CommSemiring R] (π : (i : ι) → S i → R)
    (σ : Config S) : R := ∏ i, π i (σ i)

lemma productLaw_positiveProbability (π : (i : ι) → Weight (S i))
    (hπ : ∀ i, PositiveProbability (π i)) :
    PositiveProbability (productMass π) := by
  constructor
  · intro σ
    exact Finset.prod_pos fun i _ => (hπ i).1 (σ i)
  · unfold productMass
    rw [← Fintype.prod_sum]
    simp [fun i => (hπ i).2]

omit [∀ i, Fintype (S i)] in
lemma productMass_update {R : Type*} [CommSemiring R]
    (π : (i : ι) → S i → R) (σ : Config S) (i : ι) (a : S i) :
    productMass π (Function.update σ i a) =
      π i a * ∏ j ∈ Finset.univ.erase i, π j (σ j) := by
  classical
  unfold productMass
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

omit [Fintype ι] [∀ i, Fintype (S i)] in
lemma split_update (i : ι) (r : (j : {j // j ≠ i}) → S j)
    (a b : S i) :
    Function.update ((Equiv.piSplitAt i S).symm (a, r)) i b =
      (Equiv.piSplitAt i S).symm (b, r) := by
  ext j
  by_cases h : j = i
  · subst j
    simp [Equiv.piSplitAt]
  · simp [Equiv.piSplitAt, h]

omit [∀ i, Fintype (S i)] in
lemma productMass_split {R : Type*} [CommSemiring R]
    (π : (i : ι) → S i → R) (i : ι)
    (r : (j : {j // j ≠ i}) → S j) (a : S i) :
    productMass π ((Equiv.piSplitAt i S).symm (a, r)) =
      π i a * ∏ j : {j // j ≠ i}, π j (r j) := by
  classical
  unfold productMass
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [Equiv.piSplitAt_symm_apply, dite_true]
  congr 1
  rw [Finset.prod_subtype _ (by simp : ∀ j : ι,
    j ∈ Finset.univ.erase i ↔ j ≠ i)]
  apply Finset.prod_congr rfl
  intro j _
  simp [j.property]

/-- Disintegrating a product sum into one letter and all remaining letters. -/
lemma sum_productMass_split {R : Type*} [CommSemiring R]
    (π : (i : ι) → S i → R) (i : ι) (f : Config S → R) :
    (∑ σ, productMass π σ * f σ) =
      ∑ r : (j : {j // j ≠ i}) → S j,
        (∏ j : {j // j ≠ i}, π j (r j)) *
          ∑ a, π i a * f ((Equiv.piSplitAt i S).symm (a, r)) := by
  classical
  rw [← (Equiv.piSplitAt i S).symm.sum_comp
    (fun σ => productMass π σ * f σ), Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [productMass_split]
  ring

/-- Averaging the letter at one site, with all other coordinates fixed. -/
def average {R : Type*} [CommSemiring R] (π : (i : ι) → S i → R)
    (i : ι) (f : Config S → R) (σ : Config S) : R :=
  ∑ a, π i a * f (Function.update σ i a)

omit [Fintype ι] in
lemma average_update {R : Type*} [CommSemiring R]
    (π : (i : ι) → S i → R) (i : ι) (f : Config S → R)
    (σ : Config S) (a : S i) :
    average π i f (Function.update σ i a) = average π i f σ := by
  simp [average, Function.update_idem]

lemma average_preserves_sum {R : Type*} [CommSemiring R]
    (π : (i : ι) → S i → R) (hnorm : ∀ i, ∑ a, π i a = 1)
    (i : ι) (f : Config S → R) :
    (∑ σ, productMass π σ * average π i f σ) =
      ∑ σ, productMass π σ * f σ := by
  classical
  rw [sum_productMass_split π i, sum_productMass_split π i f]
  apply Finset.sum_congr rfl
  intro r _
  simp only [average, split_update]
  rw [← Finset.sum_mul, hnorm i, one_mul]

omit [Fintype ι] in
lemma average_const {R : Type*} [CommSemiring R]
    (π : (i : ι) → S i → R) (hnorm : ∀ i, ∑ a, π i a = 1)
    (i : ι) (c : R) : average π i (fun _ => c) = (fun _ => c) := by
  funext σ
  simp [average, ← Finset.sum_mul, hnorm i]

omit [Fintype ι] in
lemma average_commute {R : Type*} [CommSemiring R]
    (π : (i : ι) → S i → R) (i j : ι) (f : Config S → R) :
    average π i (average π j f) = average π j (average π i f) := by
  classical
  by_cases hij : i = j
  · subst j
    rfl
  funext σ
  simp only [average, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  rw [Function.update_comm hij]
  ring

omit [Fintype ι] in
lemma average_sub (π : (i : ι) → Weight (S i)) (i : ι)
    (f g : Config S → ℝ) :
    average π i (fun σ => f σ - g σ) =
      (fun σ => average π i f σ - average π i g σ) := by
  funext σ
  simp [average, mul_sub, Finset.sum_sub_distrib]

end AKLT.W.GAP016
