module
public import AKLT.Uniq.BondAlgebra

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-! Site degrees of polynomial quotients and the algebraic part of `l:divisibility`. -/

noncomputable section
open scoped BigOperators
open AKLT.Challenge

namespace AKLT.Uniq

/-- A nonzero homogeneous factor cannot hide components of a different degree. -/
theorem homogeneous_quotient {S : Type*} (w : S → ℕ)
    {p q : MvPolynomial S ℂ} {a b : ℕ} (hp0 : p ≠ 0)
    (hp : p.IsWeightedHomogeneous w a)
    (hpq : (p * q).IsWeightedHomogeneous w (a + b)) :
    q.IsWeightedHomogeneous w b := by
  classical
  let A := MvPolynomial.weightedHomogeneousSubmodule ℂ w
  let _ := MvPolynomial.weightedGradedAlgebra ℂ w
  have h : p * q = p * (DirectSum.decompose A q b : MvPolynomial S ℂ) := by
    calc
      p * q = (DirectSum.decompose A (p * q) (a + b) : MvPolynomial S ℂ) :=
        (DirectSum.decompose_of_mem_same A hpq).symm
      _ = _ := DirectSum.coe_decompose_mul_add_of_left_mem A hp
  have hq := mul_left_cancel₀ hp0 h
  rw [hq]
  exact (DirectSum.decompose A q b).property

variable {L N : Size}

/-- The remaining site degrees after removing any chosen edge set. -/
def residualDegree (E : Finset (Bond L N)) (x : Site L N) : ℕ :=
  4 - ∑ e ∈ E, bondDegree e x

theorem subset_bondDegree_le_four (E : Finset (Bond L N)) (x : Site L N) :
    (∑ e ∈ E, bondDegree e x) ≤ 4 := by
  rw [← sum_bondDegree x]
  exact Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)

theorem product_siteDegrees (E : Finset (Bond L N)) :
    HasSiteDegrees (∏ e ∈ E, singlet e) (fun x => ∑ e ∈ E, bondDegree e x) := by
  intro x
  exact MvPolynomial.IsWeightedHomogeneous.prod E singlet
    (fun e => bondDegree e x) (fun e _ => singlet_siteDegrees e x)

theorem product_singlet_ne_zero (E : Finset (Bond L N)) :
    (∏ e ∈ E, singlet e) ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun e _ => (singletPrime L N e).ne_zero)

/-- Node D1: the exact multidegree of every quotient by a bond subproduct. -/
def QuotientDegreesStatement : Prop :=
  ∀ L N : Size, ∀ E : Finset (Bond L N), ∀ q : SpinorPolynomial L N,
    IsPhysical ((∏ e ∈ E, singlet e) * q) → HasSiteDegrees q (residualDegree E)

theorem quotientDegrees : QuotientDegreesStatement := by
  intro L N E q hq x
  apply homogeneous_quotient (siteWeight x) (product_singlet_ne_zero E)
    (product_siteDegrees E x)
  convert hq x using 1
  exact Nat.add_sub_of_le (subset_bondDegree_le_four E x)

/-- Node D2: the full algebraic edge-set divisibility statement with quotient degree. -/
def PolynomialDivisibilityStatement : Prop :=
  ∀ L N : Size, ∀ E : Finset (Bond L N), ∀ p : SpinorPolynomial L N,
    IsPhysical p → (∀ e ∈ E, singlet e ∣ p) →
    ∃ q : SpinorPolynomial L N,
      p = (∏ e ∈ E, singlet e) * q ∧ HasSiteDegrees q (residualDegree E)

theorem polynomialDivisibility : PolynomialDivisibilityStatement := by
  intro L N E p hp hdvd
  obtain ⟨q, hq⟩ := productDivisibility L N E p hdvd
  exact ⟨q, hq, quotientDegrees L N E q (hq ▸ hp)⟩

/-- The incident edge set `E_R` in `l:divisibility`. -/
def incidentBonds (R : Finset (Site L N)) : Finset (Bond L N) := by
  classical
  exact Finset.univ.filter (fun e => ∃ x ∈ R, x ∈ bondSites e)

/-- Independence means that neither spinor variable at the indicated sites occurs. -/
def IndependentOn (R : Finset (Site L N)) (p : SpinorPolynomial L N) : Prop :=
  ∀ x ∈ R, ∀ k : Fin 2, (x, k) ∉ p.vars

theorem incident_degree (R : Finset (Site L N)) {x : Site L N} (hx : x ∈ R) :
    (∑ e ∈ incidentBonds R, bondDegree e x) = 4 := by
  classical
  rw [← sum_bondDegree x]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro e _ he
  by_contra h
  have hinc := (bondDegree_pos_iff e x).mp (Nat.pos_of_ne_zero h)
  apply he
  simp only [incidentBonds, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨x, hx, hinc⟩

theorem independentOn_of_degrees {R : Finset (Site L N)} {q : SpinorPolynomial L N}
    (hq : HasSiteDegrees q (residualDegree (incidentBonds R))) : IndependentOn R q := by
  intro x hx k hk
  obtain ⟨d, hd, hdk⟩ := (MvPolynomial.mem_vars_iff_mem_support (x, k)).mp hk
  have hweight := hq x (MvPolynomial.mem_support_iff.mp hd)
  rw [siteWeight_degree, residualDegree, incident_degree R hx, Nat.sub_self] at hweight
  have hdk' := Finsupp.mem_support_iff.mp hdk
  fin_cases k
  · change d (x, 0) ≠ 0 at hdk'
    omega
  · change d (x, 1) ≠ 0 at hdk'
    omega

/-- Node D3: the polynomial version of `l:divisibility`, including independence on `R`. -/
def PolynomialLocalDivisibilityStatement : Prop :=
  ∀ L N : Size, ∀ R : Finset (Site L N), ∀ p : SpinorPolynomial L N,
    IsPhysical p → (∀ e ∈ incidentBonds R, singlet e ∣ p) →
    ∃ q : SpinorPolynomial L N,
      p = (∏ e ∈ incidentBonds R, singlet e) * q ∧ IndependentOn R q

theorem polynomialLocalDivisibility : PolynomialLocalDivisibilityStatement := by
  intro L N R p hp hdvd
  obtain ⟨q, hq, hdegree⟩ := polynomialDivisibility L N (incidentBonds R) p hp hdvd
  exact ⟨q, hq, independentOn_of_degrees hdegree⟩

#print axioms homogeneous_quotient
#print axioms subset_bondDegree_le_four
#print axioms product_siteDegrees
#print axioms product_singlet_ne_zero
#print axioms quotientDegrees
#print axioms polynomialDivisibility
#print axioms incident_degree
#print axioms independentOn_of_degrees
#print axioms polynomialLocalDivisibility

end AKLT.Uniq
