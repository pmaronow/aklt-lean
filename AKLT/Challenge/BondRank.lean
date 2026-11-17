module
public import AKLT.Uniq.Edge
@[expose] public section
noncomputable section
open scoped BigOperators
open AKLT.Challenge AKLT.Uniq

/-! The bond rank via the proved polynomial edge factorization.
A polynomial of site degrees d has one coordinate for each choice 0 ≤ k_x ≤ d_x.
Multiplication by the nonzero bond determinant identifies the degree-(3,3,4,…,4)
space with the kernel of P_e. Its dimension is 16·5^(LN−2); rank-nullity in the
physical Hilbert space then gives rank 9·5^(LN−2), including all spectators.
This reuses the proved edge lemma rather than introducing a numerical premise. -/
namespace AKLT.Challenge.SanityRank
variable {L N : Size}
abbrev Coordinates (d : Site L N → ℕ) := (x : Site L N) → Fin (d x + 1)
def exponent (d : Site L N → ℕ) (σ : Coordinates d) : (Site L N × Fin 2) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p => if p.2 = 0 then d p.1 - (σ p.1).val else (σ p.1).val

theorem exponent_apply (d : Site L N → ℕ) (σ : Coordinates d) (x : Site L N) (k : Fin 2) :
    exponent d σ (x,k) = if k = 0 then d x - (σ x).val else (σ x).val := by
  simp [exponent]
theorem exponent_injective (d : Site L N → ℕ) : Function.Injective (exponent d) := by
  intro σ τ h
  funext x
  apply Fin.ext
  simpa [exponent_apply] using congrArg (fun m => m (x,1)) h

theorem exponent_weight (d : Site L N → ℕ) (σ : Coordinates d) (x : Site L N) :
    Finsupp.weight (siteWeight x) (exponent d σ) = d x := by
  rw [siteWeight_degree]
  simp only [exponent_apply, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false]
  have := (σ x).isLt
  omega

theorem exists_exponent (d : Site L N → ℕ) (m : (Site L N × Fin 2) →₀ ℕ)
    (hm : ∀ x, Finsupp.weight (siteWeight x) m = d x) :
    ∃ σ : Coordinates d, exponent d σ = m := by
  have hdeg (x : Site L N) := (siteWeight_degree m x).symm.trans (hm x)
  let σ : Coordinates d := fun x => ⟨m (x,1), by have := hdeg x; omega⟩
  refine ⟨σ, ?_⟩
  ext ⟨x,k⟩
  fin_cases k
  · simp only [exponent_apply]
    change d x - m (x,1) = m (x,0)
    have := hdeg x
    omega
  · simp [exponent_apply, σ]

def gradedSpace (d : Site L N → ℕ) : Submodule ℂ (SpinorPolynomial L N) where
  carrier := {p | HasSiteDegrees p d}
  zero_mem' := fun _x => MvPolynomial.isWeightedHomogeneous_zero ℂ _ _
  add_mem' hp hq := fun x => (hp x).add (hq x)
  smul_mem' c _p hp := fun x => (MvPolynomial.weightedHomogeneousSubmodule ℂ (siteWeight x) (d x)).smul_mem c (hp x)

def polynomial (d : Site L N → ℕ) (c : Coordinates d → ℂ) : SpinorPolynomial L N :=
  ∑ σ : Coordinates d, MvPolynomial.monomial (exponent d σ) (c σ)

theorem polynomial_coeff (d : Site L N → ℕ) (c : Coordinates d → ℂ) (σ : Coordinates d) :
    (polynomial d c).coeff (exponent d σ) = c σ := by
  classical
  simp only [polynomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  simp [(exponent_injective d).eq_iff]

theorem polynomial_degrees (d : Site L N → ℕ) (c : Coordinates d → ℂ) :
    HasSiteDegrees (polynomial d c) d := by
  intro x
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro σ _
  exact MvPolynomial.isWeightedHomogeneous_monomial _ _ _ (exponent_weight d σ x)

theorem polynomial_inverse (d : Site L N → ℕ) (p : gradedSpace d) :
    polynomial d (fun σ => p.val.coeff (exponent d σ)) = p.val := by
  classical
  ext m
  by_cases h : ∃ σ : Coordinates d, exponent d σ = m
  · obtain ⟨σ,rfl⟩ := h
    exact polynomial_coeff d _ σ
  · have hz : p.val.coeff m = 0 := by
      by_contra hz
      exact h (exists_exponent d m fun x => p.property x hz)
    rw [hz]
    simp only [polynomial, MvPolynomial.coeff_sum]
    apply Finset.sum_eq_zero
    intro σ _
    rw [MvPolynomial.coeff_monomial, ite_eq_right (fun he => h ⟨σ,he⟩)]

def coordinatesEquiv (d : Site L N → ℕ) : (Coordinates d → ℂ) ≃ₗ[ℂ] gradedSpace d where
  toFun c := ⟨polynomial d c, polynomial_degrees d c⟩
  invFun p σ := p.val.coeff (exponent d σ)
  left_inv c := by ext σ; exact polynomial_coeff d c σ
  right_inv p := Subtype.ext (polynomial_inverse d p)
  map_add' c b := by
    apply Subtype.ext
    simp [polynomial, map_add, Finset.sum_add_distrib]
  map_smul' a c := by
    apply Subtype.ext
    simp [polynomial, Finset.smul_sum, MvPolynomial.smul_monomial]

theorem graded_finrank (d : Site L N → ℕ) :
    Module.finrank ℂ (gradedSpace d) = ∏ x, (d x + 1) := by
  rw [← (coordinatesEquiv d).finrank_eq]
  simp [Coordinates, Fintype.card_pi]

def decodeLinear : SpinorPolynomial L N →ₗ[ℂ] Hilbert L N where
  toFun := decode
  map_add' p q := by
    ext σ
    change (p + q).coeff (monomialDegree σ) / basisScale σ = _
    simp [decode, add_div]
  map_smul' c p := by
    ext σ
    change (c • p).coeff (monomialDegree σ) / basisScale σ = c * (p.coeff (monomialDegree σ) / basisScale σ)
    simp [mul_div_assoc]

def residualMap (e : Bond L N) : gradedSpace (edgeResidual e 1) →ₗ[ℂ] Hilbert L N where
  toFun q := decode (singlet e * q.val)
  map_add' p q := by
    change decode (singlet e * (p.val + q.val)) = _
    rw [mul_add]
    exact decodeLinear.map_add _ _
  map_smul' c q := by
    change decode (singlet e * (c • q.val)) = c • decode (singlet e * q.val)
    rw [mul_smul_comm]
    exact decodeLinear.map_smul c _

theorem residual_physical (e : Bond L N) (q : gradedSpace (edgeResidual e 1)) :
    IsPhysical (singlet e * q.val) := by
  simpa only [pow_one] using singlet_pow_mul_physical e (k := 1) (by omega) q.property

def kernelMap (e : Bond L N) : gradedSpace (edgeResidual e 1) →ₗ[ℂ] LinearMap.ker (P e) :=
  (residualMap e).codRestrict _ (fun q => by
    change P e (decode (singlet e * q.val)) = 0
    apply (edgeKernel L N e _).mpr
    rw [encode_decode (residual_physical e q)]
    exact dvd_mul_right _ _)

theorem kernelMap_bijective (e : Bond L N) : Function.Bijective (kernelMap e) := by
  constructor
  · intro q r h
    apply Subtype.ext
    apply mul_left_cancel₀ (singletPrime L N e).ne_zero
    have hv := congrArg (fun v : LinearMap.ker (P e) => encode v.val) h
    change encode (decode (singlet e * q.val)) = encode (decode (singlet e * r.val)) at hv
    simpa only [encode_decode (residual_physical e q), encode_decode (residual_physical e r)] using hv
  · intro v
    obtain ⟨q,hq,hd⟩ := (edgeFactorization L N e v.val).mp v.property
    refine ⟨⟨q,hd⟩, ?_⟩
    apply Subtype.ext
    change decode (singlet e * q) = v.val
    rw [← hq, decode_encode]

def kernelEquiv (e : Bond L N) : gradedSpace (edgeResidual e 1) ≃ₗ[ℂ] LinearMap.ker (P e) :=
  LinearEquiv.ofBijective (kernelMap e) (kernelMap_bijective e)

theorem kernel_finrank (e : Bond L N) :
    Module.finrank ℂ (LinearMap.ker (P e)) = ∏ x, (edgeResidual e 1 x + 1) := by
  rw [← (kernelEquiv e).finrank_eq, graded_finrank]

theorem residual_product (e : Bond L N) :
    (∏ x, (edgeResidual e 1 x + 1)) = 16 * 5 ^ (L.val * N.val - 2) := by
  classical
  let a := e.1
  let b := nextSite e.1 e.2
  let f := fun x => edgeResidual e 1 x + 1
  let S := ((Finset.univ : Finset (Site L N)).erase a).erase b
  have hne : b ≠ a := nextSite_ne e.1 e.2
  have ha : a ∈ (Finset.univ : Finset (Site L N)) := Finset.mem_univ a
  have hb : b ∈ (Finset.univ : Finset (Site L N)).erase a := Finset.mem_erase.mpr ⟨hne, Finset.mem_univ b⟩
  have hfa : f a = 4 := by dsimp [f,a]; rw [(edgeResidual_endpoint e 1).1]
  have hfb : f b = 4 := by dsimp [f,b]; rw [(edgeResidual_endpoint e 1).2]
  have hprod : (∏ x ∈ S, f x) = 5 ^ S.card := by
    rw [← Finset.prod_const]
    apply Finset.prod_congr rfl
    intro x hx
    have hxb : x ≠ b := (Finset.mem_erase.mp hx).1
    have hxa : x ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
    simp [f,edgeResidual,bondDegree,show e.1 ≠ x from Ne.symm hxa,
      show nextSite e.1 e.2 ≠ x from Ne.symm hxb]
  have hcard : S.card = L.val * N.val - 2 := by
    dsimp [S]
    rw [Finset.card_erase_of_mem hb, Finset.card_erase_of_mem ha, Finset.card_univ]
    have hs : Fintype.card (Site L N) = L.val * N.val := site_count L N
    omega
  calc
    (∏ x, (edgeResidual e 1 x + 1)) = f a * ∏ x ∈ (Finset.univ : Finset (Site L N)).erase a, f x :=
      (Finset.mul_prod_erase _ f ha).symm
    _ = f a * (f b * ∏ x ∈ S, f x) :=
      congrArg (fun z => f a * z) (Finset.mul_prod_erase _ f hb).symm
    _ = _ := by rw [hfa,hfb,hprod,hcard]; ring

theorem bond_rank (L N : Size) : BondRank L N := by
  intro e
  have h := LinearMap.finrank_range_add_finrank_ker (P e)
  rw [kernel_finrank, residual_product] at h
  have hd : Module.finrank ℂ (Hilbert L N) = 5 ^ (L.val * N.val) := hilbert_dimension L N
  have hn : 2 ≤ L.val * N.val := by
    have hL := L.property
    have hN := N.property
    nlinarith
  have hpow : 5 ^ (L.val * N.val) = 25 * 5 ^ (L.val * N.val - 2) := by
    calc
      5 ^ (L.val * N.val) = 5 ^ ((L.val * N.val - 2) + 2) := by congr 1; omega
      _ = _ := by rw [pow_add]; ring
  rw [hd,hpow] at h
  change Module.finrank ℂ (LinearMap.range (P e)) = 9 * 5 ^ (L.val * N.val - 2)
  omega

theorem four_by_four_nondegenerate : FourByFourNondegenerate := by
  refine ⟨bonds_haveTwoSites four four,bonds_areDistinct four four,AKLT.Uniq.B_ne_zero four four,?_⟩
  change BondRank four four
  exact bond_rank four four

#print axioms exponent_apply
#print axioms exponent_injective
#print axioms exponent_weight
#print axioms exists_exponent
#print axioms polynomial_coeff
#print axioms polynomial_degrees
#print axioms polynomial_inverse
#print axioms graded_finrank
#print axioms residual_physical
#print axioms kernelMap_bijective
#print axioms kernel_finrank
#print axioms residual_product
#print axioms bond_rank
#print axioms four_by_four_nondegenerate
end AKLT.Challenge.SanityRank
end
