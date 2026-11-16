STATUS: PROVED

Proved [`AKLT.Uniq.uniqueness`](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Main.lean:14) with the exact requested statement:

```lean
theorem uniqueness : ∀ L N : AKLT.Challenge.Size, AKLT.Challenge.B L N ≠ 0 ∧
    LinearMap.ker (AKLT.Challenge.H L N) = Submodule.span ℂ {AKLT.Challenge.B L N}
```

All 22 closed blueprint nodes have proved inhabitants. There are no remaining open nodes. The theorem quantifies over every `Size`, including odd periods and periods equal to three.

All added proof sources are under `AKLT/Uniq/`. The frozen `AKLT/Challenge/Main.lean` is unchanged. Worktree base: `13cc2a87cbc669e40cbf047d8b6e918b3056cf56`; frozen-file SHA-256: `e2d03b1b487a0f71544563eb2a2f3b242f37369bd30aab2eb3bf4738a385abcd`.

Files and roles:

| File | Role | Lines |
|---|---|---|
| [Polynomial.lean](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Polynomial.lean:1) | Normalized encode/decode, physical support, total degree, scalar quotient. | 196 |
| [Geometry.lean](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Geometry.lean:1) | Simple torus incidence count and physical multidegree of the VBS product. | 78 |
| [BondAlgebra.lean](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/BondAlgebra.lean:1) | Prime/nonassociate determinants, finite product divisibility, frozen B nonzero. | 124 |
| [Divisibility.lean](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Divisibility.lean:1) | Homogeneous quotients, incident edge products, independence of site variables. | 130 |
| [Hamiltonian.lean](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Hamiltonian.lean:1) | Energy identity and intersection of bond kernels. | 43 |
| [Casimir.lean](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Casimir.lean:1) | Adjoints, symmetry of the frozen Casimir, projection kernel as defect range. | 112 |
| [Transvectant.lean](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Transvectant.lean:1) | Euler commutator, degree lowering and a four-term right inverse. | 256 |
| [SpinCoordinates.lean](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/SpinCoordinates.lean:1) | Exact normalized single-site matrix actions, including spectators. | 321 |
| [CasimirAction.lean](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/CasimirAction.lean:1) | Differential Casimir identity and its bridge to the frozen matrices. | 108 |
| [Edge.lean](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Edge.lean:1) | Proved edge kernel and full (3,3) factorization. | 64 |
| [Blueprint.lean](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Blueprint.lean:1) | Closed target/local-divisibility nodes and proved assembly theorems. | 84 |
| [Main.lean](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Main.lean:1) | Requested unconditional theorem. | 20 |
| [Audit.lean](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Audit.lean:1) | Every exported declaration type and every theorem's axiom audit. | 253 |

The proof follows the polynomial dependency chain of §3 (`d:poly`, `l:edge`, `l:divisibility`, `p:toruskernel`):

1. `encode` multiplies Hilbert coordinates by the frozen binomial square-root factors. `decode` is exactly the coefficient formula defining `B`. Both inverse identities are proved on the physical carrier.
2. Each bond determinant is irreducible in the full multivariate polynomial ring, hence prime. Sitewise degree distinguishes nonassociate edge determinants; frozen torus simplicity excludes repeated unordered bonds. Every site has exactly four incident factors, proving physical homogeneity and non-vanishing of `B`.
3. The exact single-site spin matrices act as `2 - z₂∂₂`, `z₁∂₂`, and `z₂∂₁`. Their two-site Casimir defect is multiplication by the bond determinant followed by the transvectant Ω. Symmetry identifies the projection kernel with the defect range.
4. An explicit polynomial right inverse proves Ω is onto endpoint degree (3,3), with every spectator retained. It is `qχ/8 - q²Ωχ/112 + q³Ω²χ/2016 - q⁴Ω³χ/40320`. This replaces the paper's Cartan dimension count by an explicit algebraic surjectivity proof of the same edge image.
5. Distinct prime factors give divisibility by every incident-edge product. Graded cancellation proves the quotient has degree zero at sites in `R`, hence is independent of those variables. For all bonds, total degree forces a scalar quotient.
6. The exact energy identity gives `ker H = ⋂ ker P_e`; the preceding polynomial results give the span equality.

The proved assembly is explicit about its dependency:

```lean
theorem uniqueness_of_nodes (action : CasimirActionStatement) :
    ∀ L N : AKLT.Challenge.Size, AKLT.Challenge.B L N ≠ 0 ∧
      LinearMap.ker (AKLT.Challenge.H L N) =
        Submodule.span ℂ {AKLT.Challenge.B L N}
```

`Main.lean` supplies the proved inhabitant `casimirAction`; its complete proof is `uniqueness_of_nodes casimirAction`. Conditional helper assemblies make no unproved assumptions in the unconditional export.

Closed nodes, in a dependency-compatible inventory (every row is proved; source modules contain the supporting lemmas):

| Closed `def …Statement : Prop` | Proved inhabitant |
|---|---|
| [PolynomialCoordinatesStatement](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Polynomial.lean:129) | [polynomialCoordinates](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Polynomial.lean:135) |
| [ScalarQuotientStatement](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Polynomial.lean:160) | [scalarQuotient](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Polynomial.lean:166) |
| [TorusGeometryStatement](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Geometry.lean:41) | [torusGeometry](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Geometry.lean:46) |
| [VBSHomogeneousStatement](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Geometry.lean:59) | [vbsHomogeneous](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Geometry.lean:62) |
| [SingletPrimeStatement](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/BondAlgebra.lean:40) | [singletPrime](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/BondAlgebra.lean:43) |
| [VBSDegreeStatement](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/BondAlgebra.lean:51) | [vbsDegree](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/BondAlgebra.lean:55) |
| [SingletNonassociateStatement](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/BondAlgebra.lean:73) | [singletNonassociate](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/BondAlgebra.lean:76) |
| [ProductDivisibilityStatement](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/BondAlgebra.lean:100) | [productDivisibility](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/BondAlgebra.lean:104) |
| [QuotientDegreesStatement](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Divisibility.lean:51) | [quotientDegrees](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Divisibility.lean:55) |
| [PolynomialDivisibilityStatement](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Divisibility.lean:63) | [polynomialDivisibility](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Divisibility.lean:69) |
| [PolynomialLocalDivisibilityStatement](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Divisibility.lean:109) | [polynomialLocalDivisibility](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Divisibility.lean:115) |
| [HamiltonianKernelStatement](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Hamiltonian.lean:22) | [hamiltonianKernel](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Hamiltonian.lean:25) |
| [CasimirSymmetricStatement](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Casimir.lean:53) | [casimirSymmetric](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Casimir.lean:56) |
| [ProjectionRangeStatement](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Casimir.lean:88) | [projectionRange](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Casimir.lean:92) |
| [TransvectantSurjectiveStatement](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Transvectant.lean:222) | [transvectantSurjective](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Transvectant.lean:227) |
| [SingleSiteActionStatement](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/SpinCoordinates.lean:290) | [singleSiteAction](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/SpinCoordinates.lean:299) |
| [PolynomialCasimirStatement](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/CasimirAction.lean:53) | [polynomialCasimir](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/CasimirAction.lean:59) |
| [CasimirActionStatement](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/CasimirAction.lean:90) | [casimirAction](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/CasimirAction.lean:94) |
| [EdgeKernelStatement](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Edge.lean:16) | [edgeKernel](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Edge.lean:38) |
| [EdgeFactorizationStatement](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Edge.lean:41) | [edgeFactorization](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Edge.lean:46) |
| [UniquenessStatement](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Blueprint.lean:17) | [uniqueness](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Main.lean:14) |
| [LocalDivisibilityStatement](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Blueprint.lean:52) | [localDivisibility](/home/ubuntu/aklt/wt/ARCH_UNIQ/AKLT/Uniq/Blueprint.lean:76) |

The largest proof module is 321 lines, including declarations and axiom checks. The normalization, differential algebra, projection, UFD, and quotient arguments are separated into reusable nodes within the requested approximate proof-size bound.

Exact closed node statements follow. These snippets are in namespace `AKLT.Uniq` with `open AKLT.Challenge`; helper definitions have complete elaborated types in the declaration inventory.

```lean
def PolynomialCoordinatesStatement : Prop :=
  ∀ L N : Size,
    (∀ v : Hilbert L N, decode (encode v) = v) ∧
    (∀ p : SpinorPolynomial L N, IsPhysical p → encode (decode p) = p) ∧
    (∀ v : Hilbert L N, IsPhysical (encode v))

def ScalarQuotientStatement : Prop :=
  ∀ L N : Size, ∀ p : SpinorPolynomial L N, IsPhysical p →
    (vbsPolynomial L N).totalDegree = 4 * Fintype.card (Site L N) →
    vbsPolynomial L N ≠ 0 →
    vbsPolynomial L N ∣ p → ∃ c : ℂ, p = c • vbsPolynomial L N

def TorusGeometryStatement : Prop :=
  ∀ L N : Size, Function.Injective (@bondSites L N) ∧
    (∀ e : Bond L N, e.1 ≠ nextSite e.1 e.2) ∧
    ∀ x : Site L N, ∑ e : Bond L N, bondDegree e x = 4

def VBSHomogeneousStatement : Prop :=
  ∀ L N : Size, IsPhysical (vbsPolynomial L N)

def SingletPrimeStatement : Prop :=
  ∀ L N : Size, ∀ e : Bond L N, Prime (singlet e)

def VBSDegreeStatement : Prop :=
  ∀ L N : Size, vbsPolynomial L N ≠ 0 ∧
    (vbsPolynomial L N).totalDegree = 4 * Fintype.card (Site L N)

def SingletNonassociateStatement : Prop :=
  ∀ L N : Size, ∀ e f : Bond L N, e ≠ f → ¬ Associated (singlet e) (singlet f)

def ProductDivisibilityStatement : Prop :=
  ∀ L N : Size, ∀ E : Finset (Bond L N), ∀ p : SpinorPolynomial L N,
    (∀ e ∈ E, singlet e ∣ p) → (∏ e ∈ E, singlet e) ∣ p

def QuotientDegreesStatement : Prop :=
  ∀ L N : Size, ∀ E : Finset (Bond L N), ∀ q : SpinorPolynomial L N,
    IsPhysical ((∏ e ∈ E, singlet e) * q) → HasSiteDegrees q (residualDegree E)

def PolynomialDivisibilityStatement : Prop :=
  ∀ L N : Size, ∀ E : Finset (Bond L N), ∀ p : SpinorPolynomial L N,
    IsPhysical p → (∀ e ∈ E, singlet e ∣ p) →
    ∃ q : SpinorPolynomial L N,
      p = (∏ e ∈ E, singlet e) * q ∧ HasSiteDegrees q (residualDegree E)

def PolynomialLocalDivisibilityStatement : Prop :=
  ∀ L N : Size, ∀ R : Finset (Site L N), ∀ p : SpinorPolynomial L N,
    IsPhysical p → (∀ e ∈ incidentBonds R, singlet e ∣ p) →
    ∃ q : SpinorPolynomial L N,
      p = (∏ e ∈ incidentBonds R, singlet e) * q ∧ IndependentOn R q

def HamiltonianKernelStatement : Prop :=
  ∀ L N : Size, ∀ v : Hilbert L N, H L N v = 0 ↔ ∀ e : Bond L N, P e v = 0

def CasimirSymmetricStatement : Prop :=
  ∀ L N : Size, ∀ e : Bond L N, (bondCasimir e).IsSymmetric

def ProjectionRangeStatement : Prop :=
  ∀ L N : Size, ∀ e : Bond L N,
    LinearMap.ker (P e) = LinearMap.range (casimirDefect e)

def TransvectantSurjectiveStatement : Prop :=
  ∀ L N : Size, ∀ e : Bond L N, ∀ q : SpinorPolynomial L N,
    IsPhysical (singlet e * q) →
    ∃ v : Hilbert L N, transvectant e (encode v) = q

def SingleSiteActionStatement : Prop :=
  ∀ L N : Size, ∀ x : Site L N, ∀ v : Hilbert L N,
    encode (atSite spinZ x v) = (2 : ℂ) • encode v -
      MvPolynomial.X (x, 1) * MvPolynomial.pderiv (x, 1) (encode v) ∧
    encode (atSite spinPlus x v) =
      MvPolynomial.X (x, 0) * MvPolynomial.pderiv (x, 1) (encode v) ∧
    encode (atSite spinMinus x v) =
      MvPolynomial.X (x, 1) * MvPolynomial.pderiv (x, 0) (encode v)

def PolynomialCasimirStatement : Prop :=
  ∀ L N : Size, ∀ e : Bond L N, ∀ p : SpinorPolynomial L N, IsPhysical p →
    (20 : ℂ) • p - (polyZ e (polyZ e p) + (1 / 2 : ℂ) •
      (polyPlus e (polyMinus e p) + polyMinus e (polyPlus e p))) =
        singlet e * transvectant e p

def CasimirActionStatement : Prop :=
  ∀ L N : Size, ∀ e : Bond L N, ∀ v : Hilbert L N,
    encode (casimirDefect e v) = singlet e * transvectant e (encode v)

def EdgeKernelStatement : Prop :=
  ∀ L N : Size, ∀ e : Bond L N, ∀ v : Hilbert L N,
    P e v = 0 ↔ singlet e ∣ encode v

def EdgeFactorizationStatement : Prop :=
  ∀ L N : Size, ∀ e : Bond L N, ∀ v : Hilbert L N,
    P e v = 0 ↔ ∃ q : SpinorPolynomial L N,
      encode v = singlet e * q ∧ HasSiteDegrees q (edgeResidual e 1)

def UniquenessStatement : Prop :=
  ∀ L N : Size, B L N ≠ 0 ∧
    LinearMap.ker (H L N) = Submodule.span ℂ {B L N}

def LocalDivisibilityStatement : Prop :=
  ∀ L N : Size, ∀ R : Finset (Site L N), ∀ v : Hilbert L N,
    (∀ e ∈ incidentBonds R, P e v = 0) →
    ∃ q : SpinorPolynomial L N,
      encode v = (∏ e ∈ incidentBonds R, singlet e) * q ∧ IndependentOn R q

```

All 146 exported declaration types, including all 103 theorem statements and implicit binders, are in [declarations.log](declarations.log). [declarations.md](declarations.md) links every source signature; [declarations.json](declarations.json) is the machine-readable inventory.

Kernel axiom checks passed for every exported theorem. All 103 checks report exactly the permitted set `[propext, Classical.choice, Quot.sound]`; full output is in [axioms.log](axioms.log). The target and required assembly report:

```text
'AKLT.Uniq.uniqueness' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Uniq.uniqueness_of_nodes' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Builds used Lean 4.35.0-rc2 and the supplied linked Mathlib revision. No dependency update or Mathlib build was run. No sub-agents were used. Commands were run from the worktree with `export PATH="$HOME/.elan/bin:$PATH"`:

| Command | Wall time | Result |
|---|---:|---|
| `/usr/bin/time lake build AKLT.Uniq.Main` | 41.73 s | All proof modules built; [build-final.log](build-final.log). |
| `/usr/bin/time lake build AKLT.Uniq.Audit` | 39.61 s | Final source, including Main, built without warnings or errors; all 146 type checks and 103 axiom checks passed; [audit.log](audit.log). |
| `/usr/bin/time lake env lean AKLT/Uniq/Audit.lean` | 3.91 s | Final direct audit passed; [audit-direct.log](audit-direct.log). |

The build audit includes the last simplifier cleanup; the direct audit also checks the final audit-module comment cleanup. A lexical scan found none of the forbidden proof mechanisms. Git shows only the new `AKLT/Uniq/` directory in the worktree; all report artifacts are in the requested report directory.

Remaining open nodes and issues: none.
