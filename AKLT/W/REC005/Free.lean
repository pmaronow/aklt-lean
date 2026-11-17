import AKLT.Blueprint.Rec.NodesResponse

noncomputable section
open scoped BigOperators
open AKLT.Defs

set_option maxHeartbeats 800000
set_option maxRecDepth 2000

namespace AKLT.W.REC005

lemma golden_pos : 0 < goldenRatio := by
  unfold goldenRatio
  positivity

lemma radius_pos : 0 < icoRadius := by
  unfold icoRadius
  exact Real.sqrt_pos.2 (by linarith [golden_pos])

lemma signed_power_sum_nonneg (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ (t ^ n + (-t) ^ n) := by
  rcases Nat.even_or_odd n with h | h
  · rw [h.neg_pow]
    positivity
  · rw [h.neg_pow]
    linarith

lemma ico_monomial_nonneg (m : Fin 3 → ℕ) :
    0 ≤ moment (fun v => ∏ i, v i ^ m i) := by
  have h (a : Fin 3) :
      0 ≤ ∑ b : Fin 2, ∑ c : Fin 2,
        ∏ i : Fin 3, icoVector (a, b, c) i ^ m i := by
    fin_cases a <;>
      simp [Fin.sum_univ_two, Fin.prod_univ_three, icoVector, signValue, div_pow]
    all_goals
      have h0 := signed_power_sum_nonneg 1 (by norm_num) (m 0)
      have h1 := signed_power_sum_nonneg 1 (by norm_num) (m 1)
      have h2 := signed_power_sum_nonneg 1 (by norm_num) (m 2)
      have hg0 := signed_power_sum_nonneg goldenRatio (le_of_lt golden_pos) (m 0)
      have hg1 := signed_power_sum_nonneg goldenRatio (le_of_lt golden_pos) (m 1)
      have hg2 := signed_power_sum_nonneg goldenRatio (le_of_lt golden_pos) (m 2)
      have hr0 : 0 < icoRadius ^ m 0 := pow_pos radius_pos _
      have hr1 : 0 < icoRadius ^ m 1 := pow_pos radius_pos _
      have hr2 : 0 < icoRadius ^ m 2 := pow_pos radius_pos _
      simp only [one_pow] at h0 h1 h2
      first
      | solve | convert mul_nonneg (mul_nonneg (by positivity : 0 ≤ (0 : ℝ) ^ m 0 / icoRadius ^ m 0)
          (div_nonneg h1 (le_of_lt hr1))) (div_nonneg hg2 (le_of_lt hr2)) using 1 <;> ring
      | solve | convert mul_nonneg (mul_nonneg (div_nonneg h0 (le_of_lt hr0))
          (div_nonneg hg1 (le_of_lt hr1))) (by positivity : 0 ≤ (0 : ℝ) ^ m 2 / icoRadius ^ m 2) using 1 <;> ring
      | solve | convert mul_nonneg (mul_nonneg (div_nonneg hg0 (le_of_lt hr0))
          (by positivity : 0 ≤ (0 : ℝ) ^ m 1 / icoRadius ^ m 1)) (div_nonneg h2 (le_of_lt hr2)) using 1 <;> ring
  unfold moment
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun a _ => h a))

lemma site_monomial_nonneg (s : Status) (m : Fin 3 → ℕ) :
    0 ≤ siteFunctional s (fun v => ∏ i, v i ^ m i) := by
  have h := ico_monomial_nonneg m
  have hz : 0 ≤ ∏ i : Fin 3, (0 : Vec3) i ^ m i := by
    apply Finset.prod_nonneg
    intro i _
    exact pow_nonneg (by simp) _
  unfold moment at h
  have hh : 0 ≤ ∑ j : IcoLetter, ∏ i, icoVector j i ^ m i := by linarith
  cases s <;>
    norm_num only [siteFunctional, Fintype.sum_option, spinWeight, spinVector,
      reduceCtorEq, ↓reduceIte, zero_mul,
      Finset.sum_const_zero, zero_add, ← Finset.mul_sum]
  · exact mul_nonneg (by norm_num) hh
  · exact add_nonneg (mul_nonneg (by norm_num) hz) (mul_nonneg (by norm_num) hh)

lemma product_monomial_nonneg {ι : Type*} [Fintype ι] (s : ι → Status)
    (m : (ι × Fin 3) →₀ ℕ) :
    0 ≤ productFunctional s (fun v => ∏ z : ι × Fin 3, v z.1 z.2 ^ m z) := by
  classical
  unfold productFunctional
  simp_rw [Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (x : ι) (j : SpinLetter) =>
    spinWeight (s x) j * ∏ i : Fin 3, spinVector j i ^ m (x, i))]
  exact Finset.prod_nonneg (fun x _ => site_monomial_nonneg (s x) (fun i => m (x, i)))

def NonnegCoeffs {ι : Type*} (p : MvPolynomial ι ℝ) : Prop := ∀ m, 0 ≤ p.coeff m

lemma nonnegCoeffs_one {ι : Type*} : NonnegCoeffs (1 : MvPolynomial ι ℝ) := by
  classical
  intro m
  simp only [MvPolynomial.coeff_one]
  split_ifs <;> norm_num

lemma nonnegCoeffs_zero {ι : Type*} : NonnegCoeffs (0 : MvPolynomial ι ℝ) := by
  intro m
  simp

lemma nonnegCoeffs_X {ι : Type*} (i : ι) : NonnegCoeffs (MvPolynomial.X i : MvPolynomial ι ℝ) := by
  classical
  intro m
  simp only [MvPolynomial.coeff_X]
  split_ifs <;> norm_num

lemma nonnegCoeffs_add {ι : Type*} {p q : MvPolynomial ι ℝ}
    (hp : NonnegCoeffs p) (hq : NonnegCoeffs q) : NonnegCoeffs (p + q) := by
  intro m
  simpa using add_nonneg (hp m) (hq m)

lemma nonnegCoeffs_mul {ι : Type*} {p q : MvPolynomial ι ℝ}
    (hp : NonnegCoeffs p) (hq : NonnegCoeffs q) : NonnegCoeffs (p * q) := by
  classical
  intro m
  rw [MvPolynomial.coeff_mul]
  exact Finset.sum_nonneg (fun a _ => mul_nonneg (hp a.1) (hq a.2))

lemma nonnegCoeffs_sum {ι α : Type*} (t : Finset α) (p : α → MvPolynomial ι ℝ)
    (hp : ∀ a ∈ t, NonnegCoeffs (p a)) : NonnegCoeffs (∑ a ∈ t, p a) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using nonnegCoeffs_zero
  | @insert a t ha ih =>
    rw [Finset.sum_insert ha]
    exact nonnegCoeffs_add (hp a (by simp)) (ih (fun b hb => hp b (by simp [hb])))

lemma nonnegCoeffs_prod {ι α : Type*} (t : Finset α) (p : α → MvPolynomial ι ℝ)
    (hp : ∀ a ∈ t, NonnegCoeffs (p a)) : NonnegCoeffs (∏ a ∈ t, p a) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using nonnegCoeffs_one
  | @insert a t ha ih =>
    rw [Finset.prod_insert ha]
    exact nonnegCoeffs_mul (hp a (by simp)) (ih (fun b hb => hp b (by simp [hb])))

lemma product_polynomial_nonneg {ι : Type*} [Fintype ι] (s : ι → Status)
    (p : MvPolynomial (ι × Fin 3) ℝ) (hp : NonnegCoeffs p) :
    0 ≤ productFunctional s (fun v => MvPolynomial.eval (fun z => v z.1 z.2) p) := by
  classical
  unfold productFunctional
  simp_rw [MvPolynomial.eval_eq', Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_nonneg
  intro m hm
  have heq : (∑ n : ι → SpinLetter,
      (∏ x, spinWeight (s x) (n x)) *
        (p.coeff m * ∏ z : ι × Fin 3, spinVector (n z.1) z.2 ^ m z)) =
      p.coeff m * productFunctional s
        (fun v => ∏ z : ι × Fin 3, v z.1 z.2 ^ m z) := by
    unfold productFunctional
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [heq]
  exact mul_nonneg (hp m) (product_monomial_nonneg s m)

/-- Coordinates outside the active set evaluate to zero, just as `Network.spins` does. -/
def coordinatePoly {G : Finset Plane} (D : Network G) (x : Plane) (i : Fin 3) :
    MvPolynomial (D.active × Fin 3) ℝ :=
  if h : x ∈ D.active then MvPolynomial.X (⟨x, h⟩, i) else 0

def pairPoly {G : Finset Plane} (D : Network G) (a b : Plane) :
    MvPolynomial (D.active × Fin 3) ℝ :=
  ∑ i, coordinatePoly D a i * coordinatePoly D b i

def bondPoly {G : Finset Plane} (D : Network G) : MvPolynomial (D.active × Fin 3) ℝ :=
  ∏ e ∈ D.bonds, (1 + pairPoly D e.1 e.2)

lemma coordinatePoly_nonneg {G : Finset Plane} (D : Network G) (x : Plane) (i : Fin 3) :
    NonnegCoeffs (coordinatePoly D x i) := by
  unfold coordinatePoly
  split_ifs
  · exact nonnegCoeffs_X _
  · exact nonnegCoeffs_zero

lemma pairPoly_nonneg {G : Finset Plane} (D : Network G) (a b : Plane) :
    NonnegCoeffs (pairPoly D a b) :=
  nonnegCoeffs_sum _ _ (fun i _ =>
    nonnegCoeffs_mul (coordinatePoly_nonneg D a i) (coordinatePoly_nonneg D b i))

lemma bondPoly_nonneg {G : Finset Plane} (D : Network G) :
    NonnegCoeffs (bondPoly D) :=
  nonnegCoeffs_prod _ _ (fun e _ => nonnegCoeffs_add nonnegCoeffs_one (pairPoly_nonneg D e.1 e.2))

lemma eval_coordinatePoly {G : Finset Plane} (D : Network G)
    (n : D.active → SpinLetter) (x : Plane) (i : Fin 3) :
    MvPolynomial.eval (fun z => spinVector (n z.1) z.2) (coordinatePoly D x i) =
      D.spins n x i := by
  classical
  unfold coordinatePoly Network.spins
  split_ifs <;> simp

lemma eval_pairPoly {G : Finset Plane} (D : Network G)
    (n : D.active → SpinLetter) (a b : Plane) :
    MvPolynomial.eval (fun z => spinVector (n z.1) z.2) (pairPoly D a b) =
      dot (D.spins n a) (D.spins n b) := by
  simp [pairPoly, dot, eval_coordinatePoly]

lemma free_partition_nonneg {G : Finset Plane} (D : Network G) (τ : PinAssignment G) :
    0 ≤ D.partition τ false (fun _ => 1) := by
  have h := product_polynomial_nonneg (fun x : D.active => D.status x) (bondPoly D)
    (bondPoly_nonneg D)
  convert h using 1
  simp only [Network.partition, Bool.false_eq_true, false_and, ↓reduceIte,
    Finset.prod_const_one, mul_one, productFunctional, bondPoly, map_prod, map_add,
    map_one, eval_pairPoly]
  congr 2
  exact Subsingleton.elim _ _

lemma free_pair_partition_nonneg {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (a b : Plane) : 0 ≤ D.partition τ false (fun n => dot (n a) (n b)) := by
  have h := product_polynomial_nonneg (fun x : D.active => D.status x)
    (bondPoly D * pairPoly D a b)
    (nonnegCoeffs_mul (bondPoly_nonneg D) (pairPoly_nonneg D a b))
  convert h using 1
  simp only [Network.partition, Bool.false_eq_true, false_and, ↓reduceIte,
    Finset.prod_const_one, mul_one, productFunctional, bondPoly, map_mul, map_prod,
    map_add, map_one, eval_pairPoly]
  congr 1
  · congr 1
    exact Subsingleton.elim _ _
  · funext n
    ring

/-- In this concrete common alphabet, coordinate-sign symmetry gives free pair
positivity without a degree restriction. -/
theorem free_pair_mean_nonneg {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (a b : Plane) : 0 ≤ D.expectation τ false (fun n => dot (n a) (n b)) :=
  div_nonneg (free_pair_partition_nonneg D τ a b) (free_partition_nonneg D τ)

end AKLT.W.REC005
