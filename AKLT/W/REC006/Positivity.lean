module
public import AKLT.Blueprint.Rec.NodesResponse

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC006

/-- Averaging either sign gives a nonnegative moment in every degree. -/
theorem sign_power_sum_nonneg (k : ℕ) :
    0 ≤ ∑ j : Fin 2, signValue j ^ k := by
  rw [Fin.sum_univ_two]
  simp only [signValue, Fin.isValue, ite_true, one_pow, Fin.reduceEq, ite_false]
  rcases Nat.even_or_odd k with h | h
  · rw [h.neg_one_pow]; norm_num
  · rw [h.neg_one_pow]; norm_num

/-- The independent signs of the two nonzero coordinates give positive
monomial averages; the zero coordinate is harmless, including exponent zero. -/
theorem two_sign_moment_nonneg (p q r : ℕ) :
    0 ≤ ∑ b : Fin 2, ∑ c : Fin 2,
      (0 : ℝ)^p * (signValue b / icoRadius)^q *
        (signValue c * goldenRatio / icoRadius)^r := by
  have hφ : 0 ≤ goldenRatio := by
    unfold goldenRatio
    positivity
  have hR : 0 ≤ icoRadius := Real.sqrt_nonneg _
  have hEq :
      (∑ b : Fin 2, ∑ c : Fin 2,
        (0 : ℝ)^p * (signValue b / icoRadius)^q *
          (signValue c * goldenRatio / icoRadius)^r) =
      (0 : ℝ)^p * (icoRadius⁻¹)^q * (goldenRatio / icoRadius)^r *
        (∑ b : Fin 2, signValue b ^ q) *
        (∑ c : Fin 2, signValue c ^ r) := by
    simp only [div_eq_mul_inv, mul_pow, Fin.sum_univ_two]
    ring
  rw [hEq]
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _)
      (pow_nonneg (inv_nonneg.mpr hR) _)) (pow_nonneg (div_nonneg hφ hR) _))
      (sign_power_sum_nonneg q)) (sign_power_sum_nonneg r)

/-- For this concrete alphabet, every coordinate monomial has nonnegative
average, without a restriction on its degree. -/
theorem ico_monomial_nonneg (m : Fin 3 → ℕ) :
    0 ≤ ∑ j : IcoLetter, ∏ i : Fin 3, icoVector j i ^ m i := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_nonneg
  intro a _
  rw [Fintype.sum_prod_type]
  fin_cases a
  · simpa [icoVector, Fin.prod_univ_three] using
      two_sign_moment_nonneg (m 0) (m 1) (m 2)
  · simpa [icoVector, Fin.prod_univ_three, mul_comm, mul_left_comm, mul_assoc] using
      two_sign_moment_nonneg (m 2) (m 0) (m 1)
  · simpa [icoVector, Fin.prod_univ_three, mul_comm, mul_left_comm, mul_assoc] using
      two_sign_moment_nonneg (m 1) (m 2) (m 0)

/-- U, D, and even the omitted X law have nonnegative monomial functionals. -/
theorem site_monomial_nonneg (s : Status) (m : Fin 3 → ℕ) :
    0 ≤ siteFunctional s (fun v => ∏ i, v i ^ m i) := by
  have h0 : 0 ≤ ∏ i : Fin 3, (0 : Vec3) i ^ m i :=
    Finset.prod_nonneg fun i _ => pow_nonneg (by simp) _
  cases s <;>
    simp [siteFunctional, Fintype.sum_option, spinWeight, spinVector,
      ← Finset.mul_sum]
  · exact ico_monomial_nonneg m
  · exact add_nonneg (mul_nonneg (by norm_num) h0)
      (mul_nonneg (by norm_num) (ico_monomial_nonneg m))

/-- Tensorization preserves the nonnegative monomial averages. Natural
coefficients record the positive expansion of the free bond factors. -/
theorem product_polynomial_nonneg {ι : Type*} [Fintype ι]
    (s : ι → Status) (p : MvPolynomial (ι × Fin 3) ℕ) :
    0 ≤ productFunctional s
      (fun a => p.eval₂ (Nat.castRingHom ℝ) (fun z => a z.1 z.2)) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial m c =>
    have hm (n : ι → SpinLetter) :
        (MvPolynomial.monomial m c).eval₂ (Nat.castRingHom ℝ)
            (fun z => spinVector (n z.1) z.2) =
          (c : ℝ) * ∏ x, ∏ i : Fin 3, spinVector (n x) i ^ m (x, i) := by
      rw [MvPolynomial.eval₂_monomial,
        m.prod_fintype _ (fun _ => pow_zero _)]
      rw [Fintype.prod_prod_type]
      rfl
    unfold productFunctional
    simp_rw [hm]
    have heq :
        (∑ n : ι → SpinLetter, (∏ x, spinWeight (s x) (n x)) *
          ((c : ℝ) * ∏ x, ∏ i : Fin 3, spinVector (n x) i ^ m (x, i))) =
        (c : ℝ) * ∏ x, siteFunctional (s x) (fun v => ∏ i, v i ^ m (x, i)) := by
      simp only [siteFunctional, Fintype.prod_sum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      rw [Finset.prod_mul_distrib]
      ring
    rw [heq]
    exact mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg fun x _ =>
      site_monomial_nonneg (s x) (fun i => m (x, i)))
  | add p q hp hq =>
    simpa only [productFunctional, MvPolynomial.eval₂_add,
      mul_add, Finset.sum_add_distrib] using add_nonneg hp hq

/-- Coordinate polynomials use the same extension by zero as `Network.spins`. -/
def coordinatePolynomial {G : Finset Plane} (D : Network G) (x : Plane)
    (i : Fin 3) : MvPolynomial (D.active × Fin 3) ℕ :=
  if h : x ∈ D.active then MvPolynomial.X (⟨x, h⟩, i) else 0

def pairPolynomial {G : Finset Plane} (D : Network G) (x y : Plane) :
    MvPolynomial (D.active × Fin 3) ℕ :=
  ∑ i, coordinatePolynomial D x i * coordinatePolynomial D y i

def bondPolynomial {G : Finset Plane} (D : Network G) :
    MvPolynomial (D.active × Fin 3) ℕ :=
  ∏ e ∈ D.bonds, (1 + pairPolynomial D e.1 e.2)

theorem eval_coordinatePolynomial {G : Finset Plane} (D : Network G)
    (n : D.active → SpinLetter) (x : Plane) (i : Fin 3) :
    (coordinatePolynomial D x i).eval₂ (Nat.castRingHom ℝ)
        (fun z => spinVector (n z.1) z.2) = D.spins n x i := by
  by_cases h : x ∈ D.active <;>
    simp [coordinatePolynomial, Network.spins, h]

theorem eval_pairPolynomial {G : Finset Plane} (D : Network G)
    (n : D.active → SpinLetter) (x y : Plane) :
    (pairPolynomial D x y).eval₂ (Nat.castRingHom ℝ)
        (fun z => spinVector (n z.1) z.2) = dot (D.spins n x) (D.spins n y) := by
  simp [pairPolynomial, dot, eval_coordinatePolynomial]

theorem eval_bondPolynomial {G : Finset Plane} (D : Network G)
    (n : D.active → SpinLetter) :
    (bondPolynomial D).eval₂ (Nat.castRingHom ℝ)
        (fun z => spinVector (n z.1) z.2) =
      ∏ e ∈ D.bonds, (1 + dot (D.spins n e.1) (D.spins n e.2)) := by
  simp [bondPolynomial, eval_pairPolynomial]

/-- Free pair insertions are nonnegative in the concrete finite-spin model. -/
theorem free_pair_numerator_nonneg {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (f g : Plane) :
    0 ≤ D.partition τ false (fun a => dot (a f) (a g)) := by
  have h := product_polynomial_nonneg (fun x : D.active => D.status x.val)
    (pairPolynomial D f g * bondPolynomial D)
  convert h using 1
  simp [Network.partition, productFunctional, eval_pairPolynomial,
    eval_bondPolynomial, mul_assoc]
  congr 1
  ext
  simp

/-- The same expansion with the constant observable gives a nonnegative
normalizer. This is sufficient for the normalized nonnegativity assertion. -/
theorem free_normalizer_nonneg {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) :
    0 ≤ D.partition τ false (fun _ => 1) := by
  have h := product_polynomial_nonneg (fun x : D.active => D.status x.val)
    (bondPolynomial D)
  convert h using 1
  simp [Network.partition, productFunctional, eval_bondPolynomial]
  congr 1
  ext
  simp

/-- Normalized free scalar products are nonnegative for every network. -/
theorem free_pair_mean_nonneg {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (f g : Plane) :
    0 ≤ D.expectation τ false (fun a => dot (a f) (a g)) := by
  exact div_nonneg (free_pair_numerator_nonneg D τ f g)
    (free_normalizer_nonneg D τ)

end AKLT.W.REC006
