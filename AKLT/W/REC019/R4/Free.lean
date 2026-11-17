module
public import AKLT.W.REC019.R4.Algebra

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC019.R4

lemma pow_add_neg_nonneg (a : ℝ) (k : ℕ) : 0 ≤ a^k + (-a)^k := by
  rcases k.even_or_odd with he | ho
  · rw [he.neg_pow]
    exact add_nonneg (he.pow_nonneg a) (he.pow_nonneg a)
  · rw [ho.neg_pow]
    exact le_of_eq (add_neg_cancel _).symm

/-- The sign pairs make every coordinate monomial nonnegative after summation.
This is a direct finite calculation and holds in every degree. -/
lemma moment_monomial_nonneg (m : Fin 3 → ℕ) :
    0 ≤ moment (fun v => ∏ i, v i ^ m i) := by
  have he : moment (fun v => ∏ i, v i ^ m i) = (1 / 12 : ℝ) *
      (0 ^ m 0 * ((1 / icoRadius) ^ m 1 + (-(1 / icoRadius)) ^ m 1) *
          ((goldenRatio / icoRadius) ^ m 2 + (-(goldenRatio / icoRadius)) ^ m 2) +
       0 ^ m 2 * ((1 / icoRadius) ^ m 0 + (-(1 / icoRadius)) ^ m 0) *
          ((goldenRatio / icoRadius) ^ m 1 + (-(goldenRatio / icoRadius)) ^ m 1) +
       0 ^ m 1 * ((1 / icoRadius) ^ m 2 + (-(1 / icoRadius)) ^ m 2) *
          ((goldenRatio / icoRadius) ^ m 0 + (-(goldenRatio / icoRadius)) ^ m 0)) := by
    simp [moment, Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two,
      Fin.prod_univ_three, icoVector, signValue, neg_div]
    ring
  rw [he]
  have h1 := fun i : Fin 3 => pow_add_neg_nonneg (1 / icoRadius) (m i)
  have h2 := fun i : Fin 3 => pow_add_neg_nonneg (goldenRatio / icoRadius) (m i)
  have h10 := h1 0
  have h11 := h1 1
  have h12 := h1 2
  have h20 := h2 0
  have h21 := h2 1
  have h22 := h2 2
  positivity

lemma site_monomial_nonneg (s : Status) (m : Fin 3 → ℕ) :
    0 ≤ siteFunctional s (fun v => ∏ i, v i ^ m i) := by
  have h := moment_monomial_nonneg m
  cases s
  · simpa [siteFunctional, spinWeight, spinVector, Fintype.sum_option,
      moment, ← Finset.mul_sum] using h
  · have he : siteFunctional .D (fun v => ∏ i, v i ^ m i) =
        (3 / 5 : ℝ) * moment (fun v => ∏ i, v i ^ m i) +
          (2 / 5) * ∏ i, (0 : ℝ) ^ m i := by
      simp [siteFunctional, spinWeight, spinVector, Fintype.sum_option,
        moment, ← Finset.mul_sum]
      ring
    rw [he]
    positivity
  · simp [siteFunctional, spinWeight]

lemma product_monomial_nonneg {ι : Type*} [Fintype ι]
    (s : ι → Status) (m : (ι × Fin 3) →₀ ℕ) :
    0 ≤ productFunctional s (fun v => ∏ x, ∏ i, v x i ^ m (x, i)) := by
  classical
  have he : productFunctional s (fun v => ∏ x, ∏ i, v x i ^ m (x, i)) =
      ∏ x, siteFunctional (s x) (fun v => ∏ i, v i ^ m (x, i)) := by
    unfold productFunctional siteFunctional
    simp_rw [← Finset.prod_mul_distrib]
    exact (Fintype.prod_sum (fun x a => spinWeight (s x) a *
      ∏ i, spinVector a i ^ m (x, i))).symm
  rw [he]
  exact Finset.prod_nonneg (fun x _ => site_monomial_nonneg _ _)

/-- Positive-coefficient polynomials have nonnegative free product averages. -/
lemma free_polynomial_nonneg {ι : Type*} [Fintype ι]
    (s : ι → Status) (p : MvPolynomial (ι × Fin 3) ℕ) :
    0 ≤ productFunctional s
      (fun v => MvPolynomial.eval₂ (Nat.castRingHom ℝ) (fun z => v z.1 z.2) p) := by
  classical
  have hmon : ∀ (m : (ι × Fin 3) →₀ ℕ) (c : ℕ),
      0 ≤ productFunctional s
        (fun v => MvPolynomial.eval₂ (Nat.castRingHom ℝ) (fun z => v z.1 z.2)
          (MvPolynomial.monomial m c)) := by
    intro m c
    have hm := product_monomial_nonneg s m
    have he : productFunctional s
        (fun v => MvPolynomial.eval₂ (Nat.castRingHom ℝ) (fun z => v z.1 z.2)
          (MvPolynomial.monomial m c)) =
        c * productFunctional s (fun v => ∏ x, ∏ i, v x i ^ m (x, i)) := by
      simp only [MvPolynomial.eval₂_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
        Fintype.prod_prod_type]
      unfold productFunctional
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      change _ * ((c : ℝ) * _) = _
      ring
    rw [he]
    exact mul_nonneg (Nat.cast_nonneg c) hm
  rw [MvPolynomial.as_sum p]
  simp only [MvPolynomial.eval₂_sum]
  unfold productFunctional at *
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_nonneg (fun m _ => hmon m (p.coeff m))

/-- Coordinates for active spins, with the prescribed zero extension. -/
def networkCoordinate {G : Finset Plane} (D : Network G) (x : Plane) (i : Fin 3) :
    MvPolynomial (D.active × Fin 3) ℕ :=
  if h : x ∈ D.active then MvPolynomial.X (⟨x, h⟩, i) else 0

def networkDot {G : Finset Plane} (D : Network G) (x y : Plane) :
    MvPolynomial (D.active × Fin 3) ℕ :=
  ∑ i, networkCoordinate D x i * networkCoordinate D y i

lemma eval_networkCoordinate {G : Finset Plane} (D : Network G)
    (n : D.active → SpinLetter) (x : Plane) (i : Fin 3) :
    MvPolynomial.eval₂ (Nat.castRingHom ℝ) (fun z => spinVector (n z.1) z.2)
      (networkCoordinate D x i) = D.spins n x i := by
  classical
  unfold networkCoordinate Network.spins
  split_ifs <;> simp

lemma eval_networkDot {G : Finset Plane} (D : Network G)
    (n : D.active → SpinLetter) (x y : Plane) :
    MvPolynomial.eval₂ (Nat.castRingHom ℝ) (fun z => spinVector (n z.1) z.2)
      (networkDot D x y) = dot (D.spins n x) (D.spins n y) := by
  simp [networkDot, dot, eval_networkCoordinate]

/-- The concrete free partition is the product quadrature of a polynomial
with natural coefficients. No degree or network-validity assumption is needed. -/
lemma network_free_pair_nonneg {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (x y : Plane) :
    0 ≤ D.partition τ false (fun v => dot (v x) (v y)) := by
  classical
  let p : MvPolynomial (D.active × Fin 3) ℕ :=
    networkDot D x y * ∏ e ∈ D.bonds, (1 + networkDot D e.1 e.2)
  have h := free_polynomial_nonneg (fun z : D.active => D.status z) p
  convert h using 1
  simp [p, productFunctional, Network.partition, eval_networkDot, mul_assoc]
  apply Finset.sum_congr (by ext; simp)
  intro n _
  rfl

lemma network_free_mass_nonneg {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) : 0 ≤ D.partition τ false (fun _ => 1) := by
  classical
  let p : MvPolynomial (D.active × Fin 3) ℕ :=
    ∏ e ∈ D.bonds, (1 + networkDot D e.1 e.2)
  have h := free_polynomial_nonneg (fun z : D.active => D.status z) p
  convert h using 1
  simp [p, productFunctional, Network.partition, eval_networkDot]
  apply Finset.sum_congr (by ext; simp)
  intro n _
  rfl

/-- Free scalar-product positivity for the actual lattice-network definition. -/
theorem removedPairMean_free_nonneg {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (y f g : Plane) :
    0 ≤ removedPairMean D τ false y f g := by
  exact div_nonneg (network_free_pair_nonneg (removeSite D y) τ f g)
    (network_free_mass_nonneg (removeSite D y) τ)


end AKLT.W.REC019.R4
