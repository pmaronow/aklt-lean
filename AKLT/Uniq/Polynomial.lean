import AKLT.Challenge.Sanity

/-!
The polynomial coordinates used in §3.  `encode` includes the square roots in
the frozen orthonormal basis.  `decode` is exactly the coefficient extraction
used to define `Challenge.B`.
-/

noncomputable section

open scoped BigOperators
open AKLT.Challenge

namespace AKLT.Uniq

variable {L N : Size}

/-- The change from orthonormal coordinates to monomial coefficients. -/
def basisScale (σ : Configuration L N) : ℂ :=
  ∏ x : Site L N, (Real.sqrt (Nat.choose 4 (σ x).val : ℝ) : ℂ)

theorem basisScale_ne_zero (σ : Configuration L N) : basisScale σ ≠ 0 :=
  basis_normalization_nonzero L N σ

/-- The sitewise weight counting both spinor variables at `x`. -/
def siteWeight (x : Site L N) (p : Site L N × Fin 2) : ℕ :=
  if p.1 = x then 1 else 0

/-- Multihomogeneity, including the zero polynomial in every degree. -/
def HasSiteDegrees (p : SpinorPolynomial L N) (d : Site L N → ℕ) : Prop :=
  ∀ x, p.IsWeightedHomogeneous (siteWeight x) (d x)

/-- The polynomial carrier of the physical Hilbert space. -/
def IsPhysical (p : SpinorPolynomial L N) : Prop := HasSiteDegrees p (fun _ => 4)

/-- Normalized Hilbert coordinates as an actual polynomial. -/
def encode : Hilbert L N →ₗ[ℂ] SpinorPolynomial L N where
  toFun v := ∑ σ : Configuration L N,
    MvPolynomial.monomial (monomialDegree σ) (basisScale σ * v σ)
  map_add' v w := by
    simp [mul_add, map_add, Finset.sum_add_distrib]
  map_smul' c v := by
    simp [mul_left_comm, Finset.smul_sum, MvPolynomial.smul_monomial]

/-- The frozen coefficient extraction, extended to every polynomial. -/
def decode (p : SpinorPolynomial L N) : Hilbert L N :=
  WithLp.toLp 2 fun σ => p.coeff (monomialDegree σ) / basisScale σ

theorem monomialDegree_apply (σ : Configuration L N) (x : Site L N) (k : Fin 2) :
    monomialDegree σ (x, k) = if k = 0 then 4 - (σ x).val else (σ x).val := by
  simp [monomialDegree]

theorem monomialDegree_injective : Function.Injective (@monomialDegree L N) := by
  intro σ τ h
  funext x
  apply Fin.ext
  have := congrArg (fun d => d (x, 1)) h
  simpa [monomialDegree_apply] using this

theorem siteWeight_degree (d : (Site L N × Fin 2) →₀ ℕ) (x : Site L N) :
    Finsupp.weight (siteWeight x) d = d (x, 0) + d (x, 1) := by
  classical
  rw [Finsupp.weight_eq_sum, Fintype.sum_prod_type]
  simp [siteWeight, Fin.sum_univ_two, eq_comm]

theorem monomialDegree_siteWeight (σ : Configuration L N) (x : Site L N) :
    Finsupp.weight (siteWeight x) (monomialDegree σ) = 4 := by
  rw [siteWeight_degree]
  simp only [monomialDegree_apply, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false]
  have := (σ x).isLt
  omega

/-- Every sitewise degree-four exponent is one of the frozen basis exponents. -/
theorem degree_four_exists_configuration (d : (Site L N × Fin 2) →₀ ℕ)
    (hd : ∀ x, Finsupp.weight (siteWeight x) d = 4) :
    ∃ σ : Configuration L N, monomialDegree σ = d := by
  have hdeg (x : Site L N) := (siteWeight_degree d x).symm.trans (hd x)
  let σ : Configuration L N := fun x => ⟨d (x, 1), by have := hdeg x; omega⟩
  refine ⟨σ, ?_⟩
  ext ⟨x, k⟩
  fin_cases k
  · simp only [monomialDegree_apply]
    change 4 - d (x, 1) = d (x, 0)
    have := hdeg x
    omega
  · simp [monomialDegree_apply, σ]

theorem coeff_encode (v : Hilbert L N) (σ : Configuration L N) :
    (encode v).coeff (monomialDegree σ) = basisScale σ * v σ := by
  classical
  simp only [encode, LinearMap.coe_mk, AddHom.coe_mk, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial]
  have hinj := @monomialDegree_injective L N
  simp [hinj.eq_iff]

theorem encode_physical (v : Hilbert L N) : IsPhysical (encode v) := by
  intro x
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro σ _
  exact MvPolynomial.isWeightedHomogeneous_monomial _ _ _ (monomialDegree_siteWeight σ x)

theorem decode_encode (v : Hilbert L N) : decode (encode v) = v := by
  ext σ
  change (encode v).coeff (monomialDegree σ) / basisScale σ = v σ
  rw [coeff_encode, mul_div_cancel_left₀ _ (basisScale_ne_zero σ)]

theorem encode_injective : Function.Injective (@encode L N) := by
  intro v w h
  simpa only [decode_encode] using congrArg decode h

theorem encode_decode {p : SpinorPolynomial L N} (hp : IsPhysical p) :
    encode (decode p) = p := by
  classical
  ext d
  by_cases hd : ∃ σ : Configuration L N, monomialDegree σ = d
  · obtain ⟨σ, rfl⟩ := hd
    rw [coeff_encode]
    exact mul_div_cancel₀ _ (basisScale_ne_zero σ)
  · have hzero : p.coeff d = 0 := by
      by_contra h
      exact hd (degree_four_exists_configuration d fun x => hp x h)
    rw [hzero]
    simp only [encode, LinearMap.coe_mk, AddHom.coe_mk, MvPolynomial.coeff_sum]
    apply Finset.sum_eq_zero
    intro σ _
    rw [MvPolynomial.coeff_monomial, ite_eq_right (fun h => hd ⟨σ, h⟩)]

/-- Node P1: the normalized polynomial identification and its exact inverse. -/
def PolynomialCoordinatesStatement : Prop :=
  ∀ L N : Size,
    (∀ v : Hilbert L N, decode (encode v) = v) ∧
    (∀ p : SpinorPolynomial L N, IsPhysical p → encode (decode p) = p) ∧
    (∀ v : Hilbert L N, IsPhysical (encode v))

theorem polynomialCoordinates : PolynomialCoordinatesStatement :=
  fun _ _ => ⟨decode_encode, fun _ => encode_decode, encode_physical⟩

theorem decode_vbs (L N : Size) : decode (vbsPolynomial L N) = B L N := rfl

/-- The total physical degree, used only to force the final quotient to be scalar. -/
theorem physical_homogeneous {p : SpinorPolynomial L N} (hp : IsPhysical p) :
    p.IsHomogeneous (4 * Fintype.card (Site L N)) := by
  classical
  intro d hd
  rw [Finsupp.weight_eq_sum, Fintype.sum_prod_type]
  simp only [Pi.one_apply, smul_eq_mul, mul_one, Fin.sum_univ_two]
  calc
    ∑ x : Site L N, (d (x, 0) + d (x, 1)) = ∑ _x : Site L N, 4 := by
      apply Finset.sum_congr rfl
      intro x _
      exact (siteWeight_degree d x).symm.trans (hp x hd)
    _ = 4 * Fintype.card (Site L N) := by simp [Nat.mul_comm]

theorem physical_totalDegree_le {p : SpinorPolynomial L N} (hp : IsPhysical p) :
    p.totalDegree ≤ 4 * Fintype.card (Site L N) :=
  (physical_homogeneous hp).totalDegree_le

/-- Node P2: a physical multiple of the full bond polynomial has scalar quotient.
The degree and nonzero premises concern explicit polynomials, not open physics. -/
def ScalarQuotientStatement : Prop :=
  ∀ L N : Size, ∀ p : SpinorPolynomial L N, IsPhysical p →
    (vbsPolynomial L N).totalDegree = 4 * Fintype.card (Site L N) →
    vbsPolynomial L N ≠ 0 →
    vbsPolynomial L N ∣ p → ∃ c : ℂ, p = c • vbsPolynomial L N

theorem scalarQuotient : ScalarQuotientStatement := by
  intro L N p hp hdegree hb hdvd
  obtain ⟨q, rfl⟩ := hdvd
  by_cases hq : q = 0
  · exact ⟨0, by simp [hq]⟩
  have hle := physical_totalDegree_le hp
  rw [MvPolynomial.totalDegree_mul_of_isDomain hb hq, hdegree] at hle
  have hqdeg : q.totalDegree = 0 := by omega
  rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hqdeg
  refine ⟨q.coeff 0, ?_⟩
  nth_rw 1 [hqdeg]
  rw [MvPolynomial.smul_eq_C_mul, mul_comm]

#print axioms basisScale_ne_zero
#print axioms monomialDegree_apply
#print axioms monomialDegree_injective
#print axioms siteWeight_degree
#print axioms monomialDegree_siteWeight
#print axioms degree_four_exists_configuration
#print axioms coeff_encode
#print axioms encode_physical
#print axioms decode_encode
#print axioms encode_injective
#print axioms encode_decode
#print axioms polynomialCoordinates
#print axioms decode_vbs
#print axioms physical_homogeneous
#print axioms physical_totalDegree_le
#print axioms scalarQuotient

end AKLT.Uniq
