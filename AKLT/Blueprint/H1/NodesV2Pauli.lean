module
public import AKLT.Blueprint.H1.NodesV2Reduction

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs

namespace AKLT.Blueprint.H1

/-- `d:Pauli`/`l:inversion`, D.5–D.6, lines 248–319 in the refereed Appendix D.
Bijection between vector-affine supported monomials and Fin-4 labels, now with
arbitrary real coefficients and arbitrary n. For n=0 or J=∅ there is one constant term. -/
def PauliExpansionStatementV2 : Prop :=
  ∀ n : ℕ, ∀ J : Finset (Fin n), ∀ p : RealVectorPolynomial n,
    VectorAffineReal p → SupportedVectorsReal J p → ∀ u : Fin n → Vec3,
      evaluateRealPolynomial p u =
        ∑ a : J → Fin 4, p.coeff (pauliExponentReal J a) *
          ∏ j : J, pauliCoordinate (u j.val) (a j)

/-- `l:inversion`, D.6; interchange finite trace/tensor sums and apply the supplied
one-slot Pauli trace equation. The real coefficient may be irrational. The
single-slot equation is mathematical input, not another leaf proposition. -/
def PauliProductTraceStatementV2 : Prop :=
  (∀ a : Fin 4, ∀ u : Vec3, (pauli a * spinDensity u).trace = (pauliCoordinate u a : ℂ)) →
  ∀ n : ℕ, ∀ J : Finset (Fin n), ∀ p : RealVectorPolynomial n, ∀ u : Fin n → Vec3,
    (pauliOperatorReal J p * productDensityReal J u).trace =
      ((∑ a : J → Fin 4, p.coeff (pauliExponentReal J a) *
        ∏ j : J, pauliCoordinate (u j.val) (a j) : ℝ) : ℂ)

/-- `l:inversion`, D.6; sign substitution preserves support and vector degree,
and polynomial/vector sign changes cancel in evaluation. The identity is valid
even for I not contained in J; the public Top contract uses I⊆J. -/
def InversionPolynomialStatementV2 : Prop :=
  ∀ n : ℕ, ∀ J I : Finset (Fin n), ∀ p : RealVectorPolynomial n,
    VectorAffineReal p → SupportedVectorsReal J p →
      VectorAffineReal (invertPolynomialReal I p) ∧ SupportedVectorsReal J (invertPolynomialReal I p) ∧
      ∀ u : Fin n → Vec3,
        evaluateRealPolynomial (invertPolynomialReal I p) (invertVectorsReal I u) = evaluateRealPolynomial p u

/-- `l:inversion`, D.6; finite tensor products of PSD densities are PSD for any
finite token count. Induct on J, split the tensor-function index, and use the
Kronecker PSD theorem. Empty J is the one-dimensional matrix [1], not a zero matrix. -/
def ProductDensityPositiveStatementV2 : Prop :=
  ∀ n : ℕ, ∀ J : Finset (Fin n), ∀ u : Fin n → Vec3,
    (∀ j ∈ J, (spinDensity (u j)).PosSemidef) → (productDensityReal J u).PosSemidef

/-- `l:inversion`, D.6; sign reversal preserves squared norms for arbitrary finite
n, including n=0. This short fact is an open leaf under the proof-ownership rule. -/
def InversionBallStatementV2 : Prop :=
  ∀ n : ℕ, ∀ I : Finset (Fin n), ∀ u : Fin n → Vec3, ∀ j : Fin n,
    normSq (invertVectorsReal I u j) = normSq (u j)

end AKLT.Blueprint.H1
