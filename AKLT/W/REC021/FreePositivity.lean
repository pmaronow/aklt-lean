module
public import AKLT.W.REC021.Moments

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC021

theorem spinWeight_nonneg (s : Status) (j : SpinLetter) : 0 ≤ spinWeight s j := by
  cases s <;> cases j <;> norm_num [spinWeight]

theorem site_U_sum (f : Vec3 → ℝ) :
    siteFunctional .U f = (1 / 12 : ℝ) * ∑ j : IcoLetter, f (icoVector j) := by
  simp [siteFunctional, spinWeight, spinVector, Fintype.sum_option, Finset.mul_sum]

theorem site_D_mix (f : Vec3 → ℝ) :
    siteFunctional .D f = (3 / 5 : ℝ) * siteFunctional .U f + (2 / 5 : ℝ) * f 0 := by
  rw [site_U_sum]
  simp only [siteFunctional, Fintype.sum_option, spinWeight, spinVector]
  norm_num
  rw [← Finset.mul_sum]
  ring

theorem site_monomial_nonneg (s : Status) (d : Fin 3 → ℕ) :
    0 ≤ siteFunctional s (fun n => ∏ k, n k ^ d k) := by
  have hu : 0 ≤ siteFunctional .U (fun n => ∏ k, n k ^ d k) := by
    have hsign (n : ℕ) : (0 : ℝ) ≤ 1 + (-1 : ℝ) ^ n := by
      rcases neg_one_pow_eq_or ℝ n with h | h <;> rw [h] <;> norm_num
    rw [site_U_sum]
    have hg := golden_pos
    have hr := radius_pos
    have he : (∑ j : IcoLetter, ∏ k : Fin 3, icoVector j k ^ d k) =
        (icoRadius⁻¹) ^ d 0 * (icoRadius⁻¹) ^ d 1 * (icoRadius⁻¹) ^ d 2 *
        ((0 : ℝ) ^ d 0 * goldenRatio ^ d 2 *
          (1 + (-1 : ℝ) ^ d 1) * (1 + (-1 : ℝ) ^ d 2) +
        (0 : ℝ) ^ d 2 * goldenRatio ^ d 1 *
          (1 + (-1 : ℝ) ^ d 0) * (1 + (-1 : ℝ) ^ d 1) +
        (0 : ℝ) ^ d 1 * goldenRatio ^ d 0 *
          (1 + (-1 : ℝ) ^ d 0) * (1 + (-1 : ℝ) ^ d 2)) := by
      norm_num [Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two,
        Fin.prod_univ_three, icoVector, signValue, div_pow]
      simp only [neg_pow goldenRatio (d 0), neg_pow goldenRatio (d 1), neg_pow goldenRatio (d 2)]
      ring
    rw [he]
    have := hsign (d 0)
    have := hsign (d 1)
    have := hsign (d 2)
    positivity
  cases s with
  | U => exact hu
  | D =>
    rw [site_D_mix]
    exact add_nonneg (mul_nonneg (by norm_num) hu)
      (mul_nonneg (by norm_num) (Finset.prod_nonneg fun _ _ => pow_nonneg (by norm_num) _))
  | X => simp [siteFunctional, spinWeight, Fintype.sum_option]

/-- Natural-coefficient polynomials have nonnegative free integrals. No degree
restriction is needed, since this concrete alphabet has coordinate reflections. -/
theorem product_polynomial_nonneg {ι : Type*} [Fintype ι] (s : ι → Status)
    (p : MvPolynomial (ι × Fin 3) ℕ) :
    0 ≤ productFunctional s
      (fun n => MvPolynomial.eval₂ (Nat.castRingHom ℝ) (fun v => n v.1 v.2) p) := by
  classical
  have hm (d : (ι × Fin 3) →₀ ℕ) (c : ℕ) :
      0 ≤ productFunctional s
        (fun n => MvPolynomial.eval₂ (Nat.castRingHom ℝ) (fun v => n v.1 v.2)
          (MvPolynomial.monomial d c)) := by
    simp only [productFunctional, MvPolynomial.eval₂_monomial]
    change 0 ≤ ∑ n : ι → SpinLetter, (∏ x, spinWeight (s x) (n x)) *
      ((c : ℝ) * d.prod (fun v k => spinVector (n v.1) v.2 ^ k))
    have he (n : ι → SpinLetter) :
        d.prod (fun v k => spinVector (n v.1) v.2 ^ k) =
          ∏ x : ι, ∏ k : Fin 3, spinVector (n x) k ^ d (x, k) := by
      rw [Finsupp.prod_fintype]
      · exact Fintype.prod_prod_type _
      · intro v
        simp
    simp_rw [he]
    simp_rw [show ∀ n : ι → SpinLetter,
      (∏ x, spinWeight (s x) (n x)) *
        ((c : ℝ) * ∏ x : ι, ∏ k : Fin 3, spinVector (n x) k ^ d (x, k)) =
        (c : ℝ) * ∏ x : ι,
          (spinWeight (s x) (n x) * ∏ k : Fin 3, spinVector (n x) k ^ d (x, k)) by
          intro n; rw [Finset.prod_mul_distrib]; ring]
    rw [← Finset.mul_sum, ← Fintype.prod_sum (fun x (j : SpinLetter) =>
      spinWeight (s x) j * ∏ k : Fin 3, spinVector j k ^ d (x, k))]
    apply mul_nonneg (Nat.cast_nonneg c)
    exact Finset.prod_nonneg fun x _ => site_monomial_nonneg (s x) (fun k => d (x, k))
  have hsum := p.as_sum
  rw [hsum]
  simp only [MvPolynomial.eval₂_sum, productFunctional, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_nonneg fun d _ => hm d (p.coeff d)

def spinPolynomial {G : Finset Plane} (D : Network G) (x : Plane) (k : Fin 3) :
    MvPolynomial (D.active × Fin 3) ℕ :=
  if h : x ∈ D.active then MvPolynomial.X (⟨x, h⟩, k) else 0

def dotPolynomial {G : Finset Plane} (D : Network G) (x y : Plane) :
    MvPolynomial (D.active × Fin 3) ℕ :=
  ∑ k : Fin 3, spinPolynomial D x k * spinPolynomial D y k

theorem eval_spinPolynomial {G : Finset Plane} (D : Network G)
    (n : D.active → SpinLetter) (x : Plane) (k : Fin 3) :
    MvPolynomial.eval₂ (Nat.castRingHom ℝ) (fun v => spinVector (n v.1) v.2)
      (spinPolynomial D x k) = D.spins n x k := by
  classical
  by_cases h : x ∈ D.active <;> simp [spinPolynomial, Network.spins, h]

theorem eval_dotPolynomial {G : Finset Plane} (D : Network G)
    (n : D.active → SpinLetter) (x y : Plane) :
    MvPolynomial.eval₂ (Nat.castRingHom ℝ) (fun v => spinVector (n v.1) v.2)
      (dotPolynomial D x y) = dot (D.spins n x) (D.spins n y) := by
  classical
  simp [dotPolynomial, dot, eval_spinPolynomial]

theorem network_free_partition_nonneg {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) : 0 ≤ D.partition τ false (fun _ => 1) := by
  classical
  have h := product_polynomial_nonneg (fun x : D.active => D.status x)
    (∏ e ∈ D.bonds, (1 + dotPolynomial D e.1 e.2))
  convert h using 1 <;>
    simp [productFunctional, Network.partition, eval_dotPolynomial] <;> congr 1 <;> ext n <;> simp

theorem network_free_pair_partition_nonneg {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (a b : Plane) :
    0 ≤ D.partition τ false (fun n => dot (n a) (n b)) := by
  classical
  have h := product_polynomial_nonneg (fun x : D.active => D.status x)
    (dotPolynomial D a b * ∏ e ∈ D.bonds, (1 + dotPolynomial D e.1 e.2))
  convert h using 1 <;>
    simp [productFunctional, Network.partition, eval_dotPolynomial, mul_assoc] <;> congr 1 <;> ext n <;> simp

theorem network_free_pair_nonneg {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (a b : Plane) :
    0 ≤ D.expectation τ false (fun n => dot (n a) (n b)) :=
  div_nonneg (network_free_pair_partition_nonneg D τ a b)
    (network_free_partition_nonneg D τ)

theorem responseI_free_lower {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (y o f g : Plane) : 1 ≤ responseI D τ false y o f g := by
  have h1 := network_free_pair_nonneg (removeSite D y) τ f g
  have h2 := network_free_pair_nonneg (removeSite D y) τ f o
  have h3 := network_free_pair_nonneg (removeSite D y) τ g o
  dsimp [responseI, removedPairMean]
  linarith

#print axioms site_monomial_nonneg
#print axioms product_polynomial_nonneg
#print axioms network_free_pair_nonneg
#print axioms responseI_free_lower

end AKLT.W.REC021
