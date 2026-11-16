import AKLT.Uniq.Geometry

/-!
Prime, nonassociate bond determinants and finite-product divisibility.
These statements are independent of the spin operators.
-/

noncomputable section
open scoped BigOperators
open AKLT.Challenge

namespace AKLT.Uniq

variable {L N : Size}

theorem singlet_irreducible (e : Bond L N) : Irreducible (singlet e) := by
  classical
  let x := e.1
  let y := nextSite e.1 e.2
  have hxy : x ≠ y := (nextSite_ne e.1 e.2).symm
  have hrel : IsRelPrime (MvPolynomial.X (x, 0) : SpinorPolynomial L N)
      (-(MvPolynomial.X (x, 1) * MvPolynomial.X (y, 0))) := by
    apply IsRelPrime.neg_right
    apply MvPolynomial.X_prime.irreducible.isRelPrime_iff_not_dvd.mpr
    simp [MvPolynomial.X_dvd_mul_iff, MvPolynomial.X_dvd_X, hxy]
  have hvars : (y, (1 : Fin 2)) ∉
      (-(MvPolynomial.X (x, 1) * MvPolynomial.X (y, 0)) : SpinorPolynomial L N).vars := by
    rw [MvPolynomial.vars_neg]
    intro h
    have := MvPolynomial.vars_mul (MvPolynomial.X (x, 1) : SpinorPolynomial L N)
      (MvPolynomial.X (y, 0)) h
    simp [MvPolynomial.vars_X, Ne.symm hxy] at this
  simpa only [singlet, x, y, sub_eq_add_neg] using
    MvPolynomial.irreducible_mul_X_add
      (MvPolynomial.X (x, 0) : SpinorPolynomial L N)
      (-(MvPolynomial.X (x, 1) * MvPolynomial.X (y, 0))) (y, 1)
      (MvPolynomial.X_ne_zero _) (by simp [MvPolynomial.vars_X, Ne.symm hxy]) hvars hrel

/-- Node A1: each determinant is prime in the full polynomial ring. -/
def SingletPrimeStatement : Prop :=
  ∀ L N : Size, ∀ e : Bond L N, Prime (singlet e)

theorem singletPrime : SingletPrimeStatement :=
  fun _ _ e => (singlet_irreducible e).prime

theorem vbsPolynomial_ne_zero (L N : Size) : vbsPolynomial L N ≠ 0 := by
  classical
  exact Finset.prod_ne_zero_iff.mpr (fun e _ => (singletPrime L N e).ne_zero)

/-- Node A2: the product has the full physical degree and is nonzero. -/
def VBSDegreeStatement : Prop :=
  ∀ L N : Size, vbsPolynomial L N ≠ 0 ∧
    (vbsPolynomial L N).totalDegree = 4 * Fintype.card (Site L N)

theorem vbsDegree : VBSDegreeStatement :=
  fun L N => ⟨vbsPolynomial_ne_zero L N,
    (physical_homogeneous (vbsHomogeneous L N)).totalDegree (vbsPolynomial_ne_zero L N)⟩

/-- Non-vanishing is proved for the frozen vector, including its coordinate extraction. -/
theorem B_ne_zero (L N : Size) : B L N ≠ 0 := by
  intro h
  apply vbsPolynomial_ne_zero L N
  rw [← encode_B, h, map_zero]

theorem bondDegree_pos_iff (e : Bond L N) (x : Site L N) :
    0 < bondDegree e x ↔ x ∈ bondSites e := by
  classical
  by_cases hx : e.1 = x <;> by_cases hy : nextSite e.1 e.2 = x <;>
    simp [bondDegree, bondSites, hx, hy, eq_comm]
  exact ⟨Ne.symm hx, Ne.symm hy⟩

/-- Node A3: different unoriented torus edges give nonassociate determinants. -/
def SingletNonassociateStatement : Prop :=
  ∀ L N : Size, ∀ e f : Bond L N, e ≠ f → ¬ Associated (singlet e) (singlet f)

theorem singletNonassociate : SingletNonassociateStatement := by
  classical
  intro L N e f hef hassoc
  obtain ⟨u, hu⟩ := hassoc
  obtain ⟨c, _hc, huc⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp u.isUnit
  have hdeg (x : Site L N) : bondDegree e x = bondDegree f x := by
    have hhom : (singlet f).IsWeightedHomogeneous (siteWeight x) (bondDegree e x) := by
      rw [← hu, huc, mul_comm]
      exact (singlet_siteDegrees e x).C_mul c
    exact hhom.inj_right (singletPrime L N f).ne_zero (singlet_siteDegrees f x)
  apply hef
  apply bonds_areDistinct L N
  ext x
  rw [← bondDegree_pos_iff, ← bondDegree_pos_iff, hdeg]

theorem singlet_pairwise_relPrime (L N : Size) :
    Pairwise (fun e f : Bond L N => IsRelPrime (singlet e) (singlet f)) := by
  intro e f hef
  apply (singlet_irreducible e).isRelPrime_iff_not_dvd.mpr
  intro h
  exact singletNonassociate L N e f hef
    ((singlet_irreducible e).associated_of_dvd (singlet_irreducible f) h)

/-- Node A4: individual bond divisibility implies product divisibility on any edge set. -/
def ProductDivisibilityStatement : Prop :=
  ∀ L N : Size, ∀ E : Finset (Bond L N), ∀ p : SpinorPolynomial L N,
    (∀ e ∈ E, singlet e ∣ p) → (∏ e ∈ E, singlet e) ∣ p

theorem productDivisibility : ProductDivisibilityStatement := by
  intro L N E p h
  exact Finset.prod_dvd_of_isRelPrime
    ((singlet_pairwise_relPrime L N).set_pairwise E) h

theorem vbsPolynomial_dvd {p : SpinorPolynomial L N}
    (h : ∀ e : Bond L N, singlet e ∣ p) : vbsPolynomial L N ∣ p :=
  productDivisibility L N Finset.univ p (fun e _ => h e)

#print axioms singlet_irreducible
#print axioms singletPrime
#print axioms vbsPolynomial_ne_zero
#print axioms vbsDegree
#print axioms B_ne_zero
#print axioms bondDegree_pos_iff
#print axioms singletNonassociate
#print axioms singlet_pairwise_relPrime
#print axioms productDivisibility
#print axioms vbsPolynomial_dvd

end AKLT.Uniq
