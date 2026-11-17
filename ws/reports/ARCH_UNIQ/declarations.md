All exported declarations in `AKLT.Uniq`; complete elaborated types are in [declarations.log](declarations.log).

Signatures below use `open AKLT.Challenge` and the enclosing implicit variables shown by the elaborated types.

[`AKLT.Uniq.basisScale`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Polynomial.lean:19)

```lean
def basisScale (σ : Configuration L N) : ℂ
```

[`AKLT.Uniq.basisScale_ne_zero`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Polynomial.lean:22)

```lean
theorem basisScale_ne_zero (σ : Configuration L N) : basisScale σ ≠ 0
```

[`AKLT.Uniq.siteWeight`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Polynomial.lean:26)

```lean
def siteWeight (x : Site L N) (p : Site L N × Fin 2) : ℕ
```

[`AKLT.Uniq.HasSiteDegrees`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Polynomial.lean:30)

```lean
def HasSiteDegrees (p : SpinorPolynomial L N) (d : Site L N → ℕ) : Prop
```

[`AKLT.Uniq.IsPhysical`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Polynomial.lean:34)

```lean
def IsPhysical (p : SpinorPolynomial L N) : Prop
```

[`AKLT.Uniq.encode`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Polynomial.lean:37)

```lean
def encode : Hilbert L N →ₗ[ℂ] SpinorPolynomial L N
```

[`AKLT.Uniq.decode`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Polynomial.lean:46)

```lean
def decode (p : SpinorPolynomial L N) : Hilbert L N
```

[`AKLT.Uniq.monomialDegree_apply`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Polynomial.lean:49)

```lean
theorem monomialDegree_apply (σ : Configuration L N) (x : Site L N) (k : Fin 2) :
    monomialDegree σ (x, k) = if k = 0 then 4 - (σ x).val else (σ x).val
```

[`AKLT.Uniq.monomialDegree_injective`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Polynomial.lean:53)

```lean
theorem monomialDegree_injective : Function.Injective (@monomialDegree L N)
```

[`AKLT.Uniq.siteWeight_degree`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Polynomial.lean:60)

```lean
theorem siteWeight_degree (d : (Site L N × Fin 2) →₀ ℕ) (x : Site L N) :
    Finsupp.weight (siteWeight x) d = d (x, 0) + d (x, 1)
```

[`AKLT.Uniq.monomialDegree_siteWeight`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Polynomial.lean:66)

```lean
theorem monomialDegree_siteWeight (σ : Configuration L N) (x : Site L N) :
    Finsupp.weight (siteWeight x) (monomialDegree σ) = 4
```

[`AKLT.Uniq.degree_four_exists_configuration`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Polynomial.lean:74)

```lean
theorem degree_four_exists_configuration (d : (Site L N × Fin 2) →₀ ℕ)
    (hd : ∀ x, Finsupp.weight (siteWeight x) d = 4) :
    ∃ σ : Configuration L N, monomialDegree σ = d
```

[`AKLT.Uniq.coeff_encode`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Polynomial.lean:88)

```lean
theorem coeff_encode (v : Hilbert L N) (σ : Configuration L N) :
    (encode v).coeff (monomialDegree σ) = basisScale σ * v σ
```

[`AKLT.Uniq.encode_physical`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Polynomial.lean:96)

```lean
theorem encode_physical (v : Hilbert L N) : IsPhysical (encode v)
```

[`AKLT.Uniq.decode_encode`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Polynomial.lean:102)

```lean
theorem decode_encode (v : Hilbert L N) : decode (encode v) = v
```

[`AKLT.Uniq.encode_injective`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Polynomial.lean:107)

```lean
theorem encode_injective : Function.Injective (@encode L N)
```

[`AKLT.Uniq.encode_decode`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Polynomial.lean:111)

```lean
theorem encode_decode {p : SpinorPolynomial L N} (hp : IsPhysical p) :
    encode (decode p) = p
```

[`AKLT.Uniq.PolynomialCoordinatesStatement`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Polynomial.lean:129)

```lean
def PolynomialCoordinatesStatement : Prop :=
  ∀ L N : Size,
    (∀ v : Hilbert L N, decode (encode v) = v) ∧
    (∀ p : SpinorPolynomial L N, IsPhysical p → encode (decode p) = p) ∧
    (∀ v : Hilbert L N, IsPhysical (encode v))
```

[`AKLT.Uniq.polynomialCoordinates`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Polynomial.lean:135)

```lean
theorem polynomialCoordinates : PolynomialCoordinatesStatement
```

[`AKLT.Uniq.decode_vbs`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Polynomial.lean:138)

```lean
theorem decode_vbs (L N : Size) : decode (vbsPolynomial L N) = B L N
```

[`AKLT.Uniq.physical_homogeneous`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Polynomial.lean:141)

```lean
theorem physical_homogeneous {p : SpinorPolynomial L N} (hp : IsPhysical p) :
    p.IsHomogeneous (4 * Fintype.card (Site L N))
```

[`AKLT.Uniq.physical_totalDegree_le`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Polynomial.lean:154)

```lean
theorem physical_totalDegree_le {p : SpinorPolynomial L N} (hp : IsPhysical p) :
    p.totalDegree ≤ 4 * Fintype.card (Site L N)
```

[`AKLT.Uniq.ScalarQuotientStatement`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Polynomial.lean:160)

```lean
def ScalarQuotientStatement : Prop :=
  ∀ L N : Size, ∀ p : SpinorPolynomial L N, IsPhysical p →
    (vbsPolynomial L N).totalDegree = 4 * Fintype.card (Site L N) →
    vbsPolynomial L N ≠ 0 →
    vbsPolynomial L N ∣ p → ∃ c : ℂ, p = c • vbsPolynomial L N
```

[`AKLT.Uniq.scalarQuotient`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Polynomial.lean:166)

```lean
theorem scalarQuotient : ScalarQuotientStatement
```

[`AKLT.Uniq.previousSite`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Geometry.lean:14)

```lean
def previousSite (x : Site L N) (d : Direction) : Site L N
```

[`AKLT.Uniq.nextSiteEquiv`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Geometry.lean:17)

```lean
def nextSiteEquiv (L N : Size) (d : Direction) : Site L N ≃ Site L N
```

[`AKLT.Uniq.nextSite_eq_iff`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Geometry.lean:23)

```lean
theorem nextSite_eq_iff (x y : Site L N) (d : Direction) :
    nextSite x d = y ↔ x = previousSite y d
```

[`AKLT.Uniq.bondDegree`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Geometry.lean:28)

```lean
def bondDegree (e : Bond L N) (x : Site L N) : ℕ
```

[`AKLT.Uniq.sum_bondDegree`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Geometry.lean:31)

```lean
theorem sum_bondDegree (x : Site L N) : ∑ e : Bond L N, bondDegree e x = 4
```

[`AKLT.Uniq.TorusGeometryStatement`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Geometry.lean:41)

```lean
def TorusGeometryStatement : Prop :=
  ∀ L N : Size, Function.Injective (@bondSites L N) ∧
    (∀ e : Bond L N, e.1 ≠ nextSite e.1 e.2) ∧
    ∀ x : Site L N, ∑ e : Bond L N, bondDegree e x = 4
```

[`AKLT.Uniq.torusGeometry`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Geometry.lean:46)

```lean
theorem torusGeometry : TorusGeometryStatement
```

[`AKLT.Uniq.singlet_siteDegrees`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Geometry.lean:50)

```lean
theorem singlet_siteDegrees (e : Bond L N) : HasSiteDegrees (singlet e) (bondDegree e)
```

[`AKLT.Uniq.VBSHomogeneousStatement`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Geometry.lean:59)

```lean
def VBSHomogeneousStatement : Prop :=
  ∀ L N : Size, IsPhysical (vbsPolynomial L N)
```

[`AKLT.Uniq.vbsHomogeneous`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Geometry.lean:62)

```lean
theorem vbsHomogeneous : VBSHomogeneousStatement
```

[`AKLT.Uniq.encode_B`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Geometry.lean:68)

```lean
theorem encode_B (L N : Size) : encode (B L N) = vbsPolynomial L N
```

[`AKLT.Uniq.singlet_irreducible`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/BondAlgebra.lean:16)

```lean
theorem singlet_irreducible (e : Bond L N) : Irreducible (singlet e)
```

[`AKLT.Uniq.SingletPrimeStatement`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/BondAlgebra.lean:40)

```lean
def SingletPrimeStatement : Prop :=
  ∀ L N : Size, ∀ e : Bond L N, Prime (singlet e)
```

[`AKLT.Uniq.singletPrime`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/BondAlgebra.lean:43)

```lean
theorem singletPrime : SingletPrimeStatement
```

[`AKLT.Uniq.vbsPolynomial_ne_zero`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/BondAlgebra.lean:46)

```lean
theorem vbsPolynomial_ne_zero (L N : Size) : vbsPolynomial L N ≠ 0
```

[`AKLT.Uniq.VBSDegreeStatement`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/BondAlgebra.lean:51)

```lean
def VBSDegreeStatement : Prop :=
  ∀ L N : Size, vbsPolynomial L N ≠ 0 ∧
    (vbsPolynomial L N).totalDegree = 4 * Fintype.card (Site L N)
```

[`AKLT.Uniq.vbsDegree`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/BondAlgebra.lean:55)

```lean
theorem vbsDegree : VBSDegreeStatement
```

[`AKLT.Uniq.B_ne_zero`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/BondAlgebra.lean:60)

```lean
theorem B_ne_zero (L N : Size) : B L N ≠ 0
```

[`AKLT.Uniq.bondDegree_pos_iff`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/BondAlgebra.lean:65)

```lean
theorem bondDegree_pos_iff (e : Bond L N) (x : Site L N) :
    0 < bondDegree e x ↔ x ∈ bondSites e
```

[`AKLT.Uniq.SingletNonassociateStatement`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/BondAlgebra.lean:73)

```lean
def SingletNonassociateStatement : Prop :=
  ∀ L N : Size, ∀ e f : Bond L N, e ≠ f → ¬ Associated (singlet e) (singlet f)
```

[`AKLT.Uniq.singletNonassociate`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/BondAlgebra.lean:76)

```lean
theorem singletNonassociate : SingletNonassociateStatement
```

[`AKLT.Uniq.singlet_pairwise_relPrime`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/BondAlgebra.lean:91)

```lean
theorem singlet_pairwise_relPrime (L N : Size) :
    Pairwise (fun e f : Bond L N => IsRelPrime (singlet e) (singlet f))
```

[`AKLT.Uniq.ProductDivisibilityStatement`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/BondAlgebra.lean:100)

```lean
def ProductDivisibilityStatement : Prop :=
  ∀ L N : Size, ∀ E : Finset (Bond L N), ∀ p : SpinorPolynomial L N,
    (∀ e ∈ E, singlet e ∣ p) → (∏ e ∈ E, singlet e) ∣ p
```

[`AKLT.Uniq.productDivisibility`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/BondAlgebra.lean:104)

```lean
theorem productDivisibility : ProductDivisibilityStatement
```

[`AKLT.Uniq.vbsPolynomial_dvd`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/BondAlgebra.lean:109)

```lean
theorem vbsPolynomial_dvd {p : SpinorPolynomial L N}
    (h : ∀ e : Bond L N, singlet e ∣ p) : vbsPolynomial L N ∣ p
```

[`AKLT.Uniq.homogeneous_quotient`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Divisibility.lean:12)

```lean
theorem homogeneous_quotient {S : Type*} (w : S → ℕ)
    {p q : MvPolynomial S ℂ} {a b : ℕ} (hp0 : p ≠ 0)
    (hp : p.IsWeightedHomogeneous w a)
    (hpq : (p * q).IsWeightedHomogeneous w (a + b)) :
    q.IsWeightedHomogeneous w b
```

[`AKLT.Uniq.residualDegree`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Divisibility.lean:32)

```lean
def residualDegree (E : Finset (Bond L N)) (x : Site L N) : ℕ
```

[`AKLT.Uniq.subset_bondDegree_le_four`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Divisibility.lean:35)

```lean
theorem subset_bondDegree_le_four (E : Finset (Bond L N)) (x : Site L N) :
    (∑ e ∈ E, bondDegree e x) ≤ 4
```

[`AKLT.Uniq.product_siteDegrees`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Divisibility.lean:40)

```lean
theorem product_siteDegrees (E : Finset (Bond L N)) :
    HasSiteDegrees (∏ e ∈ E, singlet e) (fun x => ∑ e ∈ E, bondDegree e x)
```

[`AKLT.Uniq.product_singlet_ne_zero`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Divisibility.lean:46)

```lean
theorem product_singlet_ne_zero (E : Finset (Bond L N)) :
    (∏ e ∈ E, singlet e) ≠ 0
```

[`AKLT.Uniq.QuotientDegreesStatement`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Divisibility.lean:51)

```lean
def QuotientDegreesStatement : Prop :=
  ∀ L N : Size, ∀ E : Finset (Bond L N), ∀ q : SpinorPolynomial L N,
    IsPhysical ((∏ e ∈ E, singlet e) * q) → HasSiteDegrees q (residualDegree E)
```

[`AKLT.Uniq.quotientDegrees`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Divisibility.lean:55)

```lean
theorem quotientDegrees : QuotientDegreesStatement
```

[`AKLT.Uniq.PolynomialDivisibilityStatement`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Divisibility.lean:63)

```lean
def PolynomialDivisibilityStatement : Prop :=
  ∀ L N : Size, ∀ E : Finset (Bond L N), ∀ p : SpinorPolynomial L N,
    IsPhysical p → (∀ e ∈ E, singlet e ∣ p) →
    ∃ q : SpinorPolynomial L N,
      p = (∏ e ∈ E, singlet e) * q ∧ HasSiteDegrees q (residualDegree E)
```

[`AKLT.Uniq.polynomialDivisibility`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Divisibility.lean:69)

```lean
theorem polynomialDivisibility : PolynomialDivisibilityStatement
```

[`AKLT.Uniq.incidentBonds`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Divisibility.lean:75)

```lean
def incidentBonds (R : Finset (Site L N)) : Finset (Bond L N)
```

[`AKLT.Uniq.IndependentOn`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Divisibility.lean:80)

```lean
def IndependentOn (R : Finset (Site L N)) (p : SpinorPolynomial L N) : Prop
```

[`AKLT.Uniq.incident_degree`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Divisibility.lean:83)

```lean
theorem incident_degree (R : Finset (Site L N)) {x : Site L N} (hx : x ∈ R) :
    (∑ e ∈ incidentBonds R, bondDegree e x) = 4
```

[`AKLT.Uniq.independentOn_of_degrees`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Divisibility.lean:95)

```lean
theorem independentOn_of_degrees {R : Finset (Site L N)} {q : SpinorPolynomial L N}
    (hq : HasSiteDegrees q (residualDegree (incidentBonds R))) : IndependentOn R q
```

[`AKLT.Uniq.PolynomialLocalDivisibilityStatement`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Divisibility.lean:109)

```lean
def PolynomialLocalDivisibilityStatement : Prop :=
  ∀ L N : Size, ∀ R : Finset (Site L N), ∀ p : SpinorPolynomial L N,
    IsPhysical p → (∀ e ∈ incidentBonds R, singlet e ∣ p) →
    ∃ q : SpinorPolynomial L N,
      p = (∏ e ∈ incidentBonds R, singlet e) * q ∧ IndependentOn R q
```

[`AKLT.Uniq.polynomialLocalDivisibility`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Divisibility.lean:115)

```lean
theorem polynomialLocalDivisibility : PolynomialLocalDivisibilityStatement
```

[`AKLT.Uniq.h_energy`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Hamiltonian.lean:11)

```lean
theorem h_energy (L N : Size) (v : Hilbert L N) :
    (inner ℂ (H L N v) v).re = ∑ e : Bond L N, ‖P e v‖ ^ 2
```

[`AKLT.Uniq.HamiltonianKernelStatement`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Hamiltonian.lean:22)

```lean
def HamiltonianKernelStatement : Prop :=
  ∀ L N : Size, ∀ v : Hilbert L N, H L N v = 0 ↔ ∀ e : Bond L N, P e v = 0
```

[`AKLT.Uniq.hamiltonianKernel`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Hamiltonian.lean:25)

```lean
theorem hamiltonianKernel : HamiltonianKernelStatement
```

[`AKLT.Uniq.atSite_adjoint`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Casimir.lean:16)

```lean
theorem atSite_adjoint (A : Matrix (Fin 5) (Fin 5) ℂ) (x : Site L N) :
    (atSite A x).adjoint = atSite A.conjTranspose x
```

[`AKLT.Uniq.onBond_adjoint`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Casimir.lean:36)

```lean
theorem onBond_adjoint (A : Matrix (Fin 5) (Fin 5) ℂ) (e : Bond L N) :
    (onBond A e).adjoint = onBond A.conjTranspose e
```

[`AKLT.Uniq.spinZ_hermitian`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Casimir.lean:40)

```lean
theorem spinZ_hermitian : spinZ.IsHermitian
```

[`AKLT.Uniq.onBond_Z_symmetric`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Casimir.lean:48)

```lean
theorem onBond_Z_symmetric (e : Bond L N) : (onBond spinZ e).IsSymmetric
```

[`AKLT.Uniq.CasimirSymmetricStatement`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Casimir.lean:53)

```lean
def CasimirSymmetricStatement : Prop :=
  ∀ L N : Size, ∀ e : Bond L N, (bondCasimir e).IsSymmetric
```

[`AKLT.Uniq.casimirSymmetric`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Casimir.lean:56)

```lean
theorem casimirSymmetric : CasimirSymmetricStatement
```

[`AKLT.Uniq.casimirDefect`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Casimir.lean:73)

```lean
def casimirDefect (e : Bond L N) : Module.End ℂ (Hilbert L N)
```

[`AKLT.Uniq.casimirDefect_symmetric`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Casimir.lean:76)

```lean
theorem casimirDefect_symmetric (e : Bond L N) : (casimirDefect e).IsSymmetric
```

[`AKLT.Uniq.ker_casimirDefect`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Casimir.lean:80)

```lean
theorem ker_casimirDefect (e : Bond L N) :
    LinearMap.ker (casimirDefect e) = spin4Space e
```

[`AKLT.Uniq.ProjectionRangeStatement`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Casimir.lean:88)

```lean
def ProjectionRangeStatement : Prop :=
  ∀ L N : Size, ∀ e : Bond L N,
    LinearMap.ker (P e) = LinearMap.range (casimirDefect e)
```

[`AKLT.Uniq.projectionRange`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Casimir.lean:92)

```lean
theorem projectionRange : ProjectionRangeStatement
```

[`AKLT.Uniq.projection_eq_zero_iff_range`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Casimir.lean:97)

```lean
theorem projection_eq_zero_iff_range (e : Bond L N) (v : Hilbert L N) :
    P e v = 0 ↔ ∃ w : Hilbert L N, casimirDefect e w = v
```

[`AKLT.Uniq.transvectant`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Transvectant.lean:14)

```lean
def transvectant (e : Bond L N) (p : SpinorPolynomial L N) : SpinorPolynomial L N
```

[`AKLT.Uniq.transvectant_add`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Transvectant.lean:18)

```lean
theorem transvectant_add (e : Bond L N) (p q : SpinorPolynomial L N) :
    transvectant e (p + q) = transvectant e p + transvectant e q
```

[`AKLT.Uniq.transvectant_sub`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Transvectant.lean:23)

```lean
theorem transvectant_sub (e : Bond L N) (p q : SpinorPolynomial L N) :
    transvectant e (p - q) = transvectant e p - transvectant e q
```

[`AKLT.Uniq.transvectant_smul`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Transvectant.lean:28)

```lean
theorem transvectant_smul (e : Bond L N) (c : ℂ) (p : SpinorPolynomial L N) :
    transvectant e (c • p) = c • transvectant e p
```

[`AKLT.Uniq.siteEuler`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Transvectant.lean:32)

```lean
theorem siteEuler {p : SpinorPolynomial L N} {x : Site L N} {n : ℕ}
    (hp : p.IsWeightedHomogeneous (siteWeight x) n) :
    MvPolynomial.X (x, 0) * MvPolynomial.pderiv (x, 0) p +
      MvPolynomial.X (x, 1) * MvPolynomial.pderiv (x, 1) p = n • p
```

[`AKLT.Uniq.pderiv_zero_of_site_degree_zero`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Transvectant.lean:40)

```lean
theorem pderiv_zero_of_site_degree_zero {p : SpinorPolynomial L N} {x : Site L N}
    (hp : p.IsWeightedHomogeneous (siteWeight x) 0) (k : Fin 2) :
    MvPolynomial.pderiv (x, k) p = 0
```

[`AKLT.Uniq.edgeResidual`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Transvectant.lean:56)

```lean
def edgeResidual (e : Bond L N) (k : ℕ) (x : Site L N) : ℕ
```

[`AKLT.Uniq.bondDegree_le_one`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Transvectant.lean:59)

```lean
theorem bondDegree_le_one (e : Bond L N) (x : Site L N) : bondDegree e x ≤ 1
```

[`AKLT.Uniq.edgeResidual_deriv_arithmetic`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Transvectant.lean:64)

```lean
theorem edgeResidual_deriv_arithmetic (e : Bond L N) {k : ℕ} (hk : k < 4) (x : Site L N) :
    (edgeResidual e k x - siteWeight x (nextSite e.1 e.2, 1)) +
        siteWeight x (nextSite e.1 e.2, 1) = edgeResidual e k x ∧
    edgeResidual e (k + 1) x + siteWeight x (e.1, 0) =
        edgeResidual e k x - siteWeight x (nextSite e.1 e.2, 1)
```

[`AKLT.Uniq.transvectant_degrees`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Transvectant.lean:73)

```lean
theorem transvectant_degrees (e : Bond L N) {k : ℕ} {p : SpinorPolynomial L N}
    (hk : k < 4) (hp : HasSiteDegrees p (edgeResidual e k)) :
    HasSiteDegrees (transvectant e p) (edgeResidual e (k + 1))
```

[`AKLT.Uniq.singlet_pow_mul_physical`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Transvectant.lean:83)

```lean
theorem singlet_pow_mul_physical (e : Bond L N) {k : ℕ} (hk : k ≤ 4)
    {p : SpinorPolynomial L N} (hp : HasSiteDegrees p (edgeResidual e k)) :
    IsPhysical (singlet e ^ k * p)
```

[`AKLT.Uniq.edgeResidual_endpoint`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Transvectant.lean:94)

```lean
theorem edgeResidual_endpoint (e : Bond L N) (k : ℕ) :
    edgeResidual e k e.1 = 4 - k ∧
      edgeResidual e k (nextSite e.1 e.2) = 4 - k
```

[`AKLT.Uniq.transvectant_degree_four_zero`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Transvectant.lean:100)

```lean
theorem transvectant_degree_four_zero (e : Bond L N) {p : SpinorPolynomial L N}
    (hp : HasSiteDegrees p (edgeResidual e 4)) : transvectant e p = 0
```

[`AKLT.Uniq.singlet_endpoint_degrees`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Transvectant.lean:106)

```lean
theorem singlet_endpoint_degrees (e : Bond L N) :
    (singlet e).IsWeightedHomogeneous (siteWeight e.1) 1 ∧
    (singlet e).IsWeightedHomogeneous (siteWeight (nextSite e.1 e.2)) 1
```

[`AKLT.Uniq.transvectant_singlet_mul`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Transvectant.lean:115)

```lean
theorem transvectant_singlet_mul (e : Bond L N) {p : SpinorPolynomial L N} {n : ℕ}
    (hx : p.IsWeightedHomogeneous (siteWeight e.1) n)
    (hy : p.IsWeightedHomogeneous (siteWeight (nextSite e.1 e.2)) n) :
    transvectant e (singlet e * p) = (2 * n + 2) • p + singlet e * transvectant e p
```

[`AKLT.Uniq.transvectant_singlet_pow_mul`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Transvectant.lean:128)

```lean
theorem transvectant_singlet_pow_mul (e : Bond L N) {p : SpinorPolynomial L N} {n : ℕ}
    (hx : p.IsWeightedHomogeneous (siteWeight e.1) n)
    (hy : p.IsWeightedHomogeneous (siteWeight (nextSite e.1 e.2)) n) (k : ℕ) :
    transvectant e (singlet e ^ (k + 1) * p) =
      ((k + 1) * (2 * n + k + 2)) • (singlet e ^ k * p) +
        singlet e ^ (k + 1) * transvectant e p
```

[`AKLT.Uniq.transvectantRightInverse`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Transvectant.lean:158)

```lean
def transvectantRightInverse (e : Bond L N) (p : SpinorPolynomial L N) :
    SpinorPolynomial L N
```

[`AKLT.Uniq.transvectantRightInverse_physical`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Transvectant.lean:166)

```lean
theorem transvectantRightInverse_physical (e : Bond L N) {p : SpinorPolynomial L N}
    (hp : HasSiteDegrees p (edgeResidual e 1)) :
    IsPhysical (transvectantRightInverse e p)
```

[`AKLT.Uniq.transvectant_rightInverse`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Transvectant.lean:185)

```lean
theorem transvectant_rightInverse (e : Bond L N) {p : SpinorPolynomial L N}
    (hp : HasSiteDegrees p (edgeResidual e 1)) :
    transvectant e (transvectantRightInverse e p) = p
```

[`AKLT.Uniq.TransvectantSurjectiveStatement`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Transvectant.lean:222)

```lean
def TransvectantSurjectiveStatement : Prop :=
  ∀ L N : Size, ∀ e : Bond L N, ∀ q : SpinorPolynomial L N,
    IsPhysical (singlet e * q) →
    ∃ v : Hilbert L N, transvectant e (encode v) = q
```

[`AKLT.Uniq.transvectantSurjective`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Transvectant.lean:227)

```lean
theorem transvectantSurjective : TransvectantSurjectiveStatement
```

[`AKLT.Uniq.atSite_apply`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/SpinCoordinates.lean:13)

```lean
theorem atSite_apply (A : Matrix (Fin 5) (Fin 5) ℂ) (x : Site L N)
    (v : Hilbert L N) (σ : Configuration L N) :
    atSite A x v σ = ∑ k : Fin 5, A (σ x) k * v (Function.update σ x k)
```

[`AKLT.Uniq.singleScale`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/SpinCoordinates.lean:38)

```lean
def singleScale (k : Fin 5) : ℂ
```

[`AKLT.Uniq.plus_normalization`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/SpinCoordinates.lean:40)

```lean
theorem plus_normalization (i j : Fin 5) :
    singleScale i * spinPlus i j =
      if i.val + 1 = j.val then (j.val : ℂ) * singleScale j else 0
```

[`AKLT.Uniq.minus_normalization`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/SpinCoordinates.lean:46)

```lean
theorem minus_normalization (i j : Fin 5) :
    singleScale i * spinMinus i j =
      if j.val + 1 = i.val then (4 - j.val : ℂ) * singleScale j else 0
```

[`AKLT.Uniq.spectatorScale`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/SpinCoordinates.lean:53)

```lean
def spectatorScale (σ : Configuration L N) (x : Site L N) : ℂ
```

[`AKLT.Uniq.basisScale_factor`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/SpinCoordinates.lean:56)

```lean
theorem basisScale_factor (σ : Configuration L N) (x : Site L N) :
    basisScale σ = singleScale (σ x) * spectatorScale σ x
```

[`AKLT.Uniq.basisScale_update`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/SpinCoordinates.lean:62)

```lean
theorem basisScale_update (σ : Configuration L N) (x : Site L N) (k : Fin 5) :
    basisScale (Function.update σ x k) = singleScale k * spectatorScale σ x
```

[`AKLT.Uniq.scaled_spinPlus`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/SpinCoordinates.lean:71)

```lean
theorem scaled_spinPlus (σ : Configuration L N) (x : Site L N) (k : Fin 5) :
    basisScale σ * spinPlus (σ x) k =
      if (σ x).val + 1 = k.val then (k.val : ℂ) * basisScale (Function.update σ x k)
      else 0
```

[`AKLT.Uniq.scaled_spinMinus`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/SpinCoordinates.lean:78)

```lean
theorem scaled_spinMinus (σ : Configuration L N) (x : Site L N) (k : Fin 5) :
    basisScale σ * spinMinus (σ x) k =
      if k.val + 1 = (σ x).val then (4 - k.val : ℂ) * basisScale (Function.update σ x k)
      else 0
```

[`AKLT.Uniq.physical_ext`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/SpinCoordinates.lean:85)

```lean
theorem physical_ext {p q : SpinorPolynomial L N} (hp : IsPhysical p) (hq : IsPhysical q)
    (h : ∀ σ : Configuration L N, p.coeff (monomialDegree σ) = q.coeff (monomialDegree σ)) :
    p = q
```

[`AKLT.Uniq.X_pderiv_physical`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/SpinCoordinates.lean:94)

```lean
theorem X_pderiv_physical {p : SpinorPolynomial L N} (hp : IsPhysical p)
    (x : Site L N) (a b : Fin 2) :
    IsPhysical (MvPolynomial.X (x, a) * MvPolynomial.pderiv (x, b) p)
```

[`AKLT.Uniq.coeff_X_pderiv_self`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/SpinCoordinates.lean:106)

```lean
theorem coeff_X_pderiv_self (p : SpinorPolynomial L N)
    (d : (Site L N × Fin 2) →₀ ℕ) (i : Site L N × Fin 2) :
    (MvPolynomial.X i * MvPolynomial.pderiv i p).coeff d = (d i : ℂ) * p.coeff d
```

[`AKLT.Uniq.monomialDegree_step_up`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/SpinCoordinates.lean:132)

```lean
theorem monomialDegree_step_up (σ : Configuration L N) (x : Site L N)
    (hk : (σ x).val < 4) :
    (monomialDegree σ - Finsupp.single (x, 0) 1) + Finsupp.single (x, 1) 1 =
      monomialDegree (Function.update σ x ⟨(σ x).val + 1, by omega⟩)
```

[`AKLT.Uniq.monomialDegree_step_down`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/SpinCoordinates.lean:147)

```lean
theorem monomialDegree_step_down (σ : Configuration L N) (x : Site L N)
    (hk : 0 < (σ x).val) :
    (monomialDegree σ - Finsupp.single (x, 1) 1) + Finsupp.single (x, 0) 1 =
      monomialDegree (Function.update σ x ⟨(σ x).val - 1, by have := (σ x).isLt; omega⟩)
```

[`AKLT.Uniq.coeff_encode_spinPlus`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/SpinCoordinates.lean:163)

```lean
theorem coeff_encode_spinPlus (x : Site L N) (v : Hilbert L N) (σ : Configuration L N) :
    (encode (atSite spinPlus x v)).coeff (monomialDegree σ) =
      ∑ k : Fin 5, if (σ x).val + 1 = k.val then
        (k.val : ℂ) * (encode v).coeff (monomialDegree (Function.update σ x k)) else 0
```

[`AKLT.Uniq.coeff_encode_spinMinus`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/SpinCoordinates.lean:174)

```lean
theorem coeff_encode_spinMinus (x : Site L N) (v : Hilbert L N) (σ : Configuration L N) :
    (encode (atSite spinMinus x v)).coeff (monomialDegree σ) =
      ∑ k : Fin 5, if k.val + 1 = (σ x).val then
        (4 - k.val : ℂ) * (encode v).coeff (monomialDegree (Function.update σ x k)) else 0
```

[`AKLT.Uniq.encode_spinZ`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/SpinCoordinates.lean:185)

```lean
theorem encode_spinZ (x : Site L N) (v : Hilbert L N) :
    encode (atSite spinZ x v) = (2 : ℂ) • encode v -
      MvPolynomial.X (x, 1) * MvPolynomial.pderiv (x, 1) (encode v)
```

[`AKLT.Uniq.encode_spinPlus`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/SpinCoordinates.lean:203)

```lean
theorem encode_spinPlus (x : Site L N) (v : Hilbert L N) :
    encode (atSite spinPlus x v) =
      MvPolynomial.X (x, 0) * MvPolynomial.pderiv (x, 1) (encode v)
```

[`AKLT.Uniq.encode_spinMinus`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/SpinCoordinates.lean:242)

```lean
theorem encode_spinMinus (x : Site L N) (v : Hilbert L N) :
    encode (atSite spinMinus x v) =
      MvPolynomial.X (x, 1) * MvPolynomial.pderiv (x, 0) (encode v)
```

[`AKLT.Uniq.SingleSiteActionStatement`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/SpinCoordinates.lean:290)

```lean
def SingleSiteActionStatement : Prop :=
  ∀ L N : Size, ∀ x : Site L N, ∀ v : Hilbert L N,
    encode (atSite spinZ x v) = (2 : ℂ) • encode v -
      MvPolynomial.X (x, 1) * MvPolynomial.pderiv (x, 1) (encode v) ∧
    encode (atSite spinPlus x v) =
      MvPolynomial.X (x, 0) * MvPolynomial.pderiv (x, 1) (encode v) ∧
    encode (atSite spinMinus x v) =
      MvPolynomial.X (x, 1) * MvPolynomial.pderiv (x, 0) (encode v)
```

[`AKLT.Uniq.singleSiteAction`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/SpinCoordinates.lean:299)

```lean
theorem singleSiteAction : SingleSiteActionStatement
```

[`AKLT.Uniq.pderiv_commute`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/CasimirAction.lean:13)

```lean
theorem pderiv_commute (p : SpinorPolynomial L N) (i j : Site L N × Fin 2) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j p) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i p)
```

[`AKLT.Uniq.polyZ`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/CasimirAction.lean:27)

```lean
def polyZ (e : Bond L N) (p : SpinorPolynomial L N) : SpinorPolynomial L N
```

[`AKLT.Uniq.polyPlus`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/CasimirAction.lean:32)

```lean
def polyPlus (e : Bond L N) (p : SpinorPolynomial L N) : SpinorPolynomial L N
```

[`AKLT.Uniq.polyMinus`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/CasimirAction.lean:36)

```lean
def polyMinus (e : Bond L N) (p : SpinorPolynomial L N) : SpinorPolynomial L N
```

[`AKLT.Uniq.encode_onBond_Z`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/CasimirAction.lean:40)

```lean
theorem encode_onBond_Z (e : Bond L N) (v : Hilbert L N) :
    encode (onBond spinZ e v) = polyZ e (encode v)
```

[`AKLT.Uniq.encode_onBond_plus`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/CasimirAction.lean:44)

```lean
theorem encode_onBond_plus (e : Bond L N) (v : Hilbert L N) :
    encode (onBond spinPlus e v) = polyPlus e (encode v)
```

[`AKLT.Uniq.encode_onBond_minus`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/CasimirAction.lean:48)

```lean
theorem encode_onBond_minus (e : Bond L N) (v : Hilbert L N) :
    encode (onBond spinMinus e v) = polyMinus e (encode v)
```

[`AKLT.Uniq.PolynomialCasimirStatement`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/CasimirAction.lean:53)

```lean
def PolynomialCasimirStatement : Prop :=
  ∀ L N : Size, ∀ e : Bond L N, ∀ p : SpinorPolynomial L N, IsPhysical p →
    (20 : ℂ) • p - (polyZ e (polyZ e p) + (1 / 2 : ℂ) •
      (polyPlus e (polyMinus e p) + polyMinus e (polyPlus e p))) =
        singlet e * transvectant e p
```

[`AKLT.Uniq.polynomialCasimir`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/CasimirAction.lean:59)

```lean
theorem polynomialCasimir : PolynomialCasimirStatement
```

[`AKLT.Uniq.CasimirActionStatement`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/CasimirAction.lean:90)

```lean
def CasimirActionStatement : Prop :=
  ∀ L N : Size, ∀ e : Bond L N, ∀ v : Hilbert L N,
    encode (casimirDefect e v) = singlet e * transvectant e (encode v)
```

[`AKLT.Uniq.casimirAction`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/CasimirAction.lean:94)

```lean
theorem casimirAction : CasimirActionStatement
```

[`AKLT.Uniq.EdgeKernelStatement`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Edge.lean:16)

```lean
def EdgeKernelStatement : Prop :=
  ∀ L N : Size, ∀ e : Bond L N, ∀ v : Hilbert L N,
    P e v = 0 ↔ singlet e ∣ encode v
```

[`AKLT.Uniq.edgeKernel_of_nodes`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Edge.lean:21)

```lean
theorem edgeKernel_of_nodes (action : CasimirActionStatement)
    (onto : TransvectantSurjectiveStatement) : EdgeKernelStatement
```

[`AKLT.Uniq.edgeKernel_of_action`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Edge.lean:35)

```lean
theorem edgeKernel_of_action (action : CasimirActionStatement) : EdgeKernelStatement
```

[`AKLT.Uniq.edgeKernel`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Edge.lean:38)

```lean
theorem edgeKernel : EdgeKernelStatement
```

[`AKLT.Uniq.EdgeFactorizationStatement`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Edge.lean:41)

```lean
def EdgeFactorizationStatement : Prop :=
  ∀ L N : Size, ∀ e : Bond L N, ∀ v : Hilbert L N,
    P e v = 0 ↔ ∃ q : SpinorPolynomial L N,
      encode v = singlet e * q ∧ HasSiteDegrees q (edgeResidual e 1)
```

[`AKLT.Uniq.edgeFactorization`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Edge.lean:46)

```lean
theorem edgeFactorization : EdgeFactorizationStatement
```

[`AKLT.Uniq.UniquenessStatement`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Blueprint.lean:17)

```lean
def UniquenessStatement : Prop :=
  ∀ L N : Size, B L N ≠ 0 ∧
    LinearMap.ker (H L N) = Submodule.span ℂ {B L N}
```

[`AKLT.Uniq.uniqueness_of_edge`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Blueprint.lean:22)

```lean
theorem uniqueness_of_edge (edge : EdgeKernelStatement) :
    ∀ L N : AKLT.Challenge.Size, AKLT.Challenge.B L N ≠ 0 ∧
      LinearMap.ker (AKLT.Challenge.H L N) =
        Submodule.span ℂ {AKLT.Challenge.B L N}
```

[`AKLT.Uniq.LocalDivisibilityStatement`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Blueprint.lean:52)

```lean
def LocalDivisibilityStatement : Prop :=
  ∀ L N : Size, ∀ R : Finset (Site L N), ∀ v : Hilbert L N,
    (∀ e ∈ incidentBonds R, P e v = 0) →
    ∃ q : SpinorPolynomial L N,
      encode v = (∏ e ∈ incidentBonds R, singlet e) * q ∧ IndependentOn R q
```

[`AKLT.Uniq.localDivisibility_of_edge`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Blueprint.lean:58)

```lean
theorem localDivisibility_of_edge (edge : EdgeKernelStatement) :
    LocalDivisibilityStatement
```

[`AKLT.Uniq.uniqueness_of_polynomial_nodes`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Blueprint.lean:65)

```lean
theorem uniqueness_of_polynomial_nodes (action : CasimirActionStatement)
    (onto : TransvectantSurjectiveStatement) : UniquenessStatement
```

[`AKLT.Uniq.uniqueness_of_nodes`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Blueprint.lean:70)

```lean
theorem uniqueness_of_nodes (action : CasimirActionStatement) :
    ∀ L N : AKLT.Challenge.Size, AKLT.Challenge.B L N ≠ 0 ∧
      LinearMap.ker (AKLT.Challenge.H L N) =
        Submodule.span ℂ {AKLT.Challenge.B L N}
```

[`AKLT.Uniq.localDivisibility`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Blueprint.lean:76)

```lean
theorem localDivisibility : LocalDivisibilityStatement
```

[`AKLT.Uniq.uniqueness`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Main.lean:14)

```lean
theorem uniqueness : ∀ L N : AKLT.Challenge.Size, AKLT.Challenge.B L N ≠ 0 ∧
    LinearMap.ker (AKLT.Challenge.H L N) = Submodule.span ℂ {AKLT.Challenge.B L N}
```
