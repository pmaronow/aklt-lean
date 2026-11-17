module
public import AKLT.Blueprint.Q.Definitions

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-! A second split of the representation, prime, degree, and tensor-transport
bridges. The larger propositions in NodesPolynomial/NodesStar become proved
intermediate assembly results, and are not open obligations. -/

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Challenge

namespace AKLT.Blueprint.Q

/-- `l:edge`, sec3 lines 93–101: diagonal evaluation has rank nine, hence
kernel dimension sixteen. Supply nine explicit preimages of monomials. -/
def PairDiagonalRankStatement : Prop := Module.finrank ℂ (LinearMap.ker pairDiagonal) = 16

/-- `l:edge`, lines 112–117: apply the explicit Casimir to the nine diagonal
coefficient vectors (the adjoint image); all have eigenvalue twenty. -/
def PairTopInclusionStatement : Prop :=
  (LinearMap.ker pairDiagonal)ᗮ ≤ Module.End.eigenspace pairCasimir 20

/-- `l:edge`, lines 118–124: the fixed pair Casimir has a nine-dimensional
eigenvalue-twenty space. Use its weight blocks, of sizes 1,2,3,4,5,4,3,2,1,
and check each block's nullity after subtracting 20I. -/
def PairTopDimensionStatement : Prop :=
  Module.finrank ℂ (Module.End.eigenspace pairCasimir 20) = 9

/-- `l:divisibility`, sec3 lines 154–165: the four-variable determinant is
prime. Treat it as a primitive degree-one polynomial over the other three
variables; the two coefficients have no common nonunit divisor. -/
def FourVariableDeterminantPrimeStatement : Prop :=
  Prime (MvPolynomial.X (0 : Fin 4) * MvPolynomial.X 3 -
    MvPolynomial.X 1 * MvPolynomial.X 2 : MvPolynomial (Fin 4) ℂ)

/-- `l:divisibility`, lines 154–165: adjoining the spectator variables and
renaming four distinct endpoint variables preserves this prime determinant.
The generic four-variable primality premise is written out explicitly. -/
def DeterminantPrimeEmbeddingStatement : Prop :=
  Prime (MvPolynomial.X (0 : Fin 4) * MvPolynomial.X 3 -
    MvPolynomial.X 1 * MvPolynomial.X 2 : MvPolynomial (Fin 4) ℂ) →
  ∀ L N : Size, ∀ e : Bond L N, Prime (singlet e)

/-- `l:divisibility`, sec3 lines 176–188: grading at one site is additive
under a nonzero product. If p and p*chi both have center degree four,
chi has center degree zero. Split chi into finitely many graded pieces;
injectivity of multiplication prevents cancellation across different degrees. -/
def CenterDegreeCancellationStatement : Prop :=
  ∀ L N : Size, ∀ x : Site L N, ∀ p χ : SpinorPolynomial L N, p ≠ 0 →
    (∀ m ∈ p.support, m (x, 0) + m (x, 1) = 4) →
    (∀ m ∈ (p * χ).support, m (x, 0) + m (x, 1) = 4) → independentAt x χ

/-- `l:divisibility`, lines 147–152, 178–186: the actual four-factor incident
product is nonzero and homogeneous of center degree four. This is the
geometric input to the generic degree cancellation, including period three. -/
def IncidentProductDegreeStatement : Prop :=
  ∀ L N : Size, ∀ x : Site L N, incidentProduct x ≠ 0 ∧
    ∀ m ∈ (incidentProduct x).support, m (x, 0) + m (x, 1) = 4

/-- `d:poly` and `l:divisibility`, sec3 lines 176–182: the physical coordinate
polynomial has center degree four at every site; the zero state is allowed. -/
def StateCenterDegreeStatement : Prop :=
  ∀ L N : Size, ∀ ψ : Hilbert L N, ∀ x : Site L N,
    ∀ m ∈ (statePolynomial ψ).support, m (x, 0) + m (x, 1) = 4

def starEdge {L N : Size} (x : Site L N) (j : Fin 4) : Bond L N :=
  if j = 0 then (x, 0) else if j = 1 then ((x.1 - 1, x.2), 0)
  else if j = 2 then (x, 1) else ((x.1, x.2 - 1), 1)

def casimirCopies {L N : Size} (x : Site L N) (n : ℕ)
    (U : Hilbert L N ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n × (Fin 5 → Fin 5))) : Prop :=
  ∀ j : Fin 4, ∀ ψ r s, U (bondCasimir (starEdge x j) ψ) (r, s) =
    starCasimir j (WithLp.toLp 2 (fun t => U ψ (r, t))) s

/-- `l:star`, sec3 lines 245–252: enumerate the four incident oriented bond
indices without duplication. The negative-direction bonds start at neighbors. -/
def StarEdgeEnumerationStatement : Prop :=
  ∀ L N : Size, ∀ x : Site L N, Function.Injective (starEdge x) ∧
    Finset.univ.image (starEdge x) = Finset.univ.filter (fun e => x ∈ bondSites e)

/-- `l:star`, lines 245–249: build the finite tensor-coordinate permutation
and transport only the Casimirs. Leaves at positions 1,2,3,4 are east, west,
north, south; extra edges between them at period three cause no extra terms. -/
def StarCasimirChartStatement : Prop :=
  ∀ L N : Size, ∀ x : Site L N,
    ∃ n : ℕ, ∃ U : Hilbert L N ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n × (Fin 5 → Fin 5)),
      casimirCopies x n U

/-- `l:star`, lines 245–250: an isometric Casimir chart transports each
eigenvalue-twenty orthogonal projector. Prove the eigenspace is a direct
sum of fixed-star eigenspaces and use uniqueness of orthogonal projection. -/
def StarProjectorTransportStatement : Prop :=
  ∀ L N : Size, ∀ x : Site L N, ∀ n : ℕ,
    ∀ U : Hilbert L N ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n × (Fin 5 → Fin 5)),
      casimirCopies x n U → ∀ j : Fin 4, ∀ ψ r s,
        U (P (starEdge x j) ψ) (r, s) =
          (Module.End.eigenspace (starCasimir j) 20).starProjection
            (WithLp.toLp 2 (fun t => U ψ (r, t))) s

end AKLT.Blueprint.Q
