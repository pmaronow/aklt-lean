import AKLT.Blueprint.H1.NodesReduction

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs

namespace AKLT.Blueprint.H1

/-- `d:Pauli`/`l:inversion`, lines 250–258 and 288–297; finite 2×2 algebra.
Anticommutation cancels cross terms. This does not assert positivity yet. -/
def BlochAlgebraStatement : Prop :=
  ∀ u : Vec3, (blochMatrix u).IsHermitian ∧
    blochMatrix u * blochMatrix u = (normSq u : ℂ) • 1 ∧ (blochMatrix u).trace = 0

/-- `l:inversion`, lines 288–298; diagonalize a Hermitian involution scaled by
sqrt r. Its eigenvalues lie in [-1,1]. The r=0 case needs no division. -/
def BlochPositivityStatement : Prop :=
  ∀ A : Matrix (Fin 2) (Fin 2) ℂ, A.IsHermitian → ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
    A * A = (r : ℂ) • 1 → ((1 / 2 : ℂ) • (1 + A)).PosSemidef

/-- `l:inversion`, lines 299–305; direct Pauli trace calculation, including a=0. -/
def SinglePauliTraceStatement : Prop :=
  ∀ a : Fin 4, ∀ u : Vec3, (pauli a * spinDensity u).trace = (pauliCoordinate u a : ℂ)

theorem singlePauliTrace : SinglePauliTraceStatement := by
  intro a u
  fin_cases a <;>
    simp [pauli, spinDensity, pauliCoordinate, Matrix.trace, Matrix.vecMul,
      dotProduct, Fin.sum_univ_succ, Matrix.smul_apply, Matrix.add_apply] <;>
    ring_nf <;> simp

/-- `d:Pauli`, lines 262–270; vector-affine supported monomials are exactly the
Pauli exponents. Prove both indexing directions; the empty J case is a constant. -/
def PauliExpansionStatement : Prop :=
  ∀ J : Finset (Fin 20), ∀ p : VectorPolynomial, VectorAffine p → SupportedVectors J p →
    ∀ u : Fin 20 → Vec3, evaluateReduced p u =
      ∑ a : J → Fin 4, (p.coeff (pauliExponent J a) : ℝ) * ∏ j : J, pauliCoordinate (u j.val) (a j)

/-- `l:inversion`, lines 301–309; interchange finite coefficient, matrix, and
tensor sums. The trace of the coordinate product factors into one-slot traces.
No affineness is needed here: the Pauli operator already selects its exponents. -/
def PauliProductTraceStatement : Prop :=
  (∀ a : Fin 4, ∀ u : Vec3, (pauli a * spinDensity u).trace = (pauliCoordinate u a : ℂ)) →
  ∀ J : Finset (Fin 20), ∀ p : VectorPolynomial, ∀ u : Fin 20 → Vec3,
    (pauliOperator J p * productDensity J u).trace =
      ((∑ a : J → Fin 4, (p.coeff (pauliExponent J a) : ℝ) *
        ∏ j : J, pauliCoordinate (u j.val) (a j) : ℝ) : ℂ)

/-- `l:inversion`, lines 308–313; a sign substitution preserves monomial support
and vector degree, and applying it to both the polynomial and vectors cancels.
This is true even when I is not contained in J. -/
def InversionPolynomialStatement : Prop :=
  ∀ J I : Finset (Fin 20), ∀ p : VectorPolynomial, VectorAffine p → SupportedVectors J p →
    VectorAffine (invertPolynomial I p) ∧ SupportedVectors J (invertPolynomial I p) ∧
      ∀ u : Fin 20 → Vec3, evaluateReduced (invertPolynomial I p) (invertVectors I u) = evaluateReduced p u

/-- `l:inversion`, lines 315–316; finite tensor products of PSD 2×2 matrices are
PSD. Induct by splitting one tensor coordinate, use PSD of a Kronecker product,
and transport by the function-space index equivalence. Include J=∅ explicitly. -/
def ProductDensityPositiveStatement : Prop :=
  ∀ J : Finset (Fin 20), ∀ u : Fin 20 → Vec3,
    (∀ j ∈ J, (spinDensity (u j)).PosSemidef) → (productDensity J u).PosSemidef

/-- `l:inversion`, lines 317–326; cyclically move a PSD square root of A to
write Tr(AB)=Tr(A^(1/2) B A^(1/2)); the latter matrix is PSD. No commutation
between A and B is assumed. -/
def TraceProductPositiveStatement : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n],
    ∀ A B : Matrix n n ℂ, A.PosSemidef → B.PosSemidef → 0 ≤ (A * B).trace.re

/-- Sign reversal preserves squared Euclidean norms, including zero. -/
def InversionBallStatement : Prop :=
  ∀ I : Finset (Fin 20), ∀ u : Fin 20 → Vec3, ∀ j : Fin 20,
    normSq (invertVectors I u j) = normSq (u j)

theorem inversionBall : InversionBallStatement := by
  intro I u j
  simp only [invertVectors]
  split <;> simp [normSq, dot]

end AKLT.Blueprint.H1
