module
public import AKLT.Blueprint.H1.Assembly

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-! Additive real-threshold adaptation. All earlier leaf files are frozen.
New leaf proofs, including elementary map/evaluation facts, are assigned elsewhere. -/

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs

namespace AKLT.Blueprint.H1

/-- Simultaneous O(3) invariance of a real polynomial on any finite vector family. -/
def OrthogonalInvariantV2 {n : ℕ} (p : RealVectorPolynomial n) : Prop :=
  ∀ R : Matrix (Fin 3) (Fin 3) ℝ, R.transpose * R = 1 → ∀ u : Fin n → Vec3,
    evaluateRealPolynomial p (fun j => R.mulVec (u j)) = evaluateRealPolynomial p u

/-- `c:reduce`, D.4; real coefficients are introduced only after exact rational
moment contraction. A coefficient embedding cannot introduce exponents. Prove
the support inclusions, allowing coefficients to vanish after a ring map. -/
def RationalEmbeddingStructureStatementV2 : Prop :=
  ∀ p : VectorPolynomial, ∀ J : Finset (Fin 20),
    VectorAffine p → SupportedVectors J p →
      VectorAffineReal (MvPolynomial.map (Rat.castHom ℝ) p) ∧
      SupportedVectorsReal J (MvPolynomial.map (Rat.castHom ℝ) p)

/-- `c:reduce`, D.4; evaluation after embedding rational coefficients is the
original rational-to-real evaluation. Use the composition rule for eval₂/map.
Kept open even though this is a short algebraic compatibility fact. -/
def RationalEmbeddingEvaluationStatementV2 : Prop :=
  ∀ p : VectorPolynomial, ∀ u : Fin 20 → Vec3,
    evaluateRealPolynomial (MvPolynomial.map (Rat.castHom ℝ) p) u = evaluateReduced p u

/-- `c:reduce`, D.4, lines 172–229 in the refereed Appendix D; real scalar
combinations preserve vector degree, supported tokens, and orthogonal invariance.
The scalar c is arbitrary real, including irrational values. -/
def DifferenceStructureStatementV2 : Prop :=
  ∀ J : Finset (Fin 20), ∀ p q : RealVectorPolynomial 20, ∀ c : ℝ,
    VectorAffineReal p → VectorAffineReal q → OrthogonalInvariantV2 p → OrthogonalInvariantV2 q →
    SupportedVectorsReal J p → SupportedVectorsReal J q →
      VectorAffineReal (p - MvPolynomial.C c * q) ∧
      OrthogonalInvariantV2 (p - MvPolynomial.C c * q) ∧
      SupportedVectorsReal J (p - MvPolynomial.C c * q)

/-- `c:reduce`, D.4; the real difference evaluates to current minus real c
times next. No real-to-rational conversion or rational approximation is used. -/
def DifferenceEvaluationStatementV2 : Prop :=
  ∀ π : PatternData, ∀ r : Representation, ∀ c : ℝ, ∀ u : Fin 20 → Vec3,
    evaluateRealPolynomial (reducedDifferenceReal π r c) u =
      evaluateReduced (reducedPolynomial π r false) u -
        c * evaluateReduced (reducedPolynomial π r true) u

/-- `c:reduce`, D.4, convex-extension paragraph; one coordinate of one vector
occurs at most once in each monomial. Real coefficients do not affect this
affine identity. The existing finite-product convex-extension leaf is reused. -/
def AffineEvaluationStatementV2 : Prop :=
  ∀ p : RealVectorPolynomial 20, VectorAffineReal p → SeparatelyAffine (evaluateRealPolynomial p)

/-- Assembled intermediate: properties of the exact rational current/next
partitions, before making a real scalar combination. Not another open leaf. -/
def RationalPartitionsStructureStatementV2 : Prop :=
  ∀ π : PatternData, π.Covered → ∀ r : Representation, ∀ next : Bool,
    VectorAffine (reducedPolynomial π r next) ∧ OrthogonalInvariant (reducedPolynomial π r next) ∧
      SupportedVectors (reductionVectors π r) (reducedPolynomial π r next)

/-- Assembled real counterpart of the legacy rational difference intermediate. -/
def ReducedStructureStatementV2 : Prop :=
  ∀ π : PatternData, π.Covered → ∀ r : Representation, ∀ c : ℝ,
    VectorAffineReal (reducedDifferenceReal π r c) ∧ OrthogonalInvariantV2 (reducedDifferenceReal π r c) ∧
      SupportedVectorsReal (reductionVectors π r) (reducedDifferenceReal π r c)

end AKLT.Blueprint.H1
