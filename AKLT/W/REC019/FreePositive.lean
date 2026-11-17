import AKLT.Blueprint.Rec.NodesResponse

noncomputable section

open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC019

private theorem pow_add_neg_pow_nonneg (a : ℝ) (n : ℕ) : 0 ≤ a ^ n + (-a) ^ n := by
  rcases Nat.even_or_odd n with h | h
  · rw [h.neg_pow]
    exact add_nonneg (h.pow_nonneg a) (h.pow_nonneg a)
  · rw [h.neg_pow]
    simp

/-- The icosahedron has independent coordinate sign symmetries. In particular,
all its monomial averages are nonnegative, without a degree restriction. -/
theorem ico_monomial_nonnegative (m : Fin 3 → ℕ) :
    0 ≤ ∑ j : IcoLetter, ∏ i : Fin 3, icoVector j i ^ m i := by
  let a : ℝ := 1 / icoRadius
  let b : ℝ := goldenRatio / icoRadius
  have he : (∑ j : IcoLetter, ∏ i : Fin 3, icoVector j i ^ m i) =
      0 ^ m 0 * (a ^ m 1 + (-a) ^ m 1) * (b ^ m 2 + (-b) ^ m 2) +
      (a ^ m 0 + (-a) ^ m 0) * (b ^ m 1 + (-b) ^ m 1) * 0 ^ m 2 +
      (b ^ m 0 + (-b) ^ m 0) * 0 ^ m 1 * (a ^ m 2 + (-a) ^ m 2) := by
    simp [IcoLetter, Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two,
      Fin.prod_univ_three, icoVector, signValue, a, b, neg_div]
    ring
  rw [he]
  exact add_nonneg
    (add_nonneg
      (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _)
        (pow_add_neg_pow_nonneg a _)) (pow_add_neg_pow_nonneg b _))
      (mul_nonneg (mul_nonneg (pow_add_neg_pow_nonneg a _)
        (pow_add_neg_pow_nonneg b _)) (pow_nonneg (by norm_num) _)))
    (mul_nonneg (mul_nonneg (pow_add_neg_pow_nonneg b _)
      (pow_nonneg (by norm_num) _)) (pow_add_neg_pow_nonneg a _))

theorem site_monomial_nonnegative (s : Status) (m : Fin 3 → ℕ) :
    0 ≤ siteFunctional s (fun n => ∏ i, n i ^ m i) := by
  have hico := ico_monomial_nonnegative m
  have hzero : (0 : ℝ) ≤ ∏ i : Fin 3, (0 : ℝ) ^ m i :=
    Finset.prod_nonneg fun _ _ => pow_nonneg (by norm_num) _
  cases s <;>
    simp only [siteFunctional, Fintype.sum_option, spinWeight, spinVector,
      ite_true, one_div, Pi.zero_apply]
  · rw [← Finset.mul_sum]
    positivity
  · rw [← Finset.mul_sum]
    positivity
  · simp

/-- A product site functional is nonnegative on every polynomial with natural
coefficients. This is the free scalar-product positivity used below. -/
theorem product_polynomial_nonnegative {ι : Type*} [Fintype ι]
    (s : ι → Status) (p : MvPolynomial (ι × Fin 3) ℕ) :
    0 ≤ productFunctional s (fun a =>
      MvPolynomial.eval₂ (Nat.castRingHom ℝ) (fun v => a v.1 v.2) p) := by
  classical
  have hmon (m : (ι × Fin 3) → ℕ) :
      0 ≤ ∑ σ : ι → SpinLetter,
        (∏ x, spinWeight (s x) (σ x)) *
          ∏ v : ι × Fin 3, spinVector (σ v.1) v.2 ^ m v := by
    have he : (∑ σ : ι → SpinLetter,
        (∏ x, spinWeight (s x) (σ x)) *
          ∏ v : ι × Fin 3, spinVector (σ v.1) v.2 ^ m v) =
        ∏ x, siteFunctional (s x) (fun n => ∏ i, n i ^ m (x, i)) := by
      symm
      simp only [siteFunctional]
      rw [Fintype.prod_sum]
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [Finset.prod_mul_distrib, Fintype.prod_prod_type]
    rw [he]
    exact Finset.prod_nonneg fun _ _ => site_monomial_nonnegative _ _
  simp only [productFunctional, MvPolynomial.eval₂_eq', Nat.coe_castRingHom,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_nonneg
  intro m hm
  have he : (∑ σ : ι → SpinLetter,
      (∏ x, spinWeight (s x) (σ x)) *
        ((p.coeff m : ℝ) * ∏ v, spinVector (σ v.1) v.2 ^ m v)) =
      (p.coeff m : ℝ) * ∑ σ : ι → SpinLetter,
        (∏ x, spinWeight (s x) (σ x)) *
          ∏ v, spinVector (σ v.1) v.2 ^ m v := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ hσ
    ring
  rw [he]
  exact mul_nonneg (Nat.cast_nonneg _) (hmon m)

private def coordinatePolynomial {G : Finset Plane} (D : Network G)
    (x : Plane) (i : Fin 3) : MvPolynomial (D.active × Fin 3) ℕ :=
  if h : x ∈ D.active then MvPolynomial.X (⟨x, h⟩, i) else 0

private def pairPolynomial {G : Finset Plane} (D : Network G)
    (x y : Plane) : MvPolynomial (D.active × Fin 3) ℕ :=
  ∑ i : Fin 3, coordinatePolynomial D x i * coordinatePolynomial D y i

private theorem eval_coordinatePolynomial {G : Finset Plane} (D : Network G)
    (σ : D.active → SpinLetter) (x : Plane) (i : Fin 3) :
    MvPolynomial.eval₂ (Nat.castRingHom ℝ) (fun v => spinVector (σ v.1) v.2)
      (coordinatePolynomial D x i) = D.spins σ x i := by
  by_cases hx : x ∈ D.active <;> simp [coordinatePolynomial, Network.spins, hx]

private theorem eval_pairPolynomial {G : Finset Plane} (D : Network G)
    (σ : D.active → SpinLetter) (x y : Plane) :
    MvPolynomial.eval₂ (Nat.castRingHom ℝ) (fun v => spinVector (σ v.1) v.2)
      (pairPolynomial D x y) = dot (D.spins σ x) (D.spins σ y) := by
  simp [pairPolynomial, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul,
    eval_coordinatePolynomial, dot]

theorem free_partition_nonnegative {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) : 0 ≤ D.partition τ false (fun _ => 1) := by
  classical
  have hp := product_polynomial_nonnegative (ι := ↥D.active)
    (fun x : D.active => D.status x.val)
    (∏ e ∈ D.bonds, (1 + pairPolynomial D e.1 e.2))
  simp only [productFunctional, MvPolynomial.eval₂_prod,
    MvPolynomial.eval₂_add, MvPolynomial.eval₂_one, eval_pairPolynomial] at hp
  unfold Network.partition
  simp only [Bool.false_eq_true, false_and, ite_false, Finset.prod_const_one, mul_one]
  convert hp using 1
  apply Finset.sum_congr
  · ext σ
    simp only [Finset.mem_univ]
  · intro σ hσ
    rfl

theorem free_pair_partition_nonnegative {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (x y : Plane) :
    0 ≤ D.partition τ false (fun n => dot (n x) (n y)) := by
  classical
  have hp := product_polynomial_nonnegative (ι := ↥D.active)
    (fun x : D.active => D.status x.val)
    (pairPolynomial D x y * ∏ e ∈ D.bonds, (1 + pairPolynomial D e.1 e.2))
  simp only [productFunctional, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_prod, MvPolynomial.eval₂_add, MvPolynomial.eval₂_one,
    eval_pairPolynomial] at hp
  unfold Network.partition
  simp only [Bool.false_eq_true, false_and, ite_false, Finset.prod_const_one, mul_one,
    mul_assoc]
  convert hp using 1
  apply Finset.sum_congr
  · ext σ
    simp only [Finset.mem_univ]
  · intro σ hσ
    rfl

theorem free_removedPairMean_nonnegative {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (y f g : Plane) : 0 ≤ removedPairMean D τ false y f g := by
  exact div_nonneg (free_pair_partition_nonnegative _ _ _ _) (free_partition_nonnegative _ _)

end AKLT.W.REC019
