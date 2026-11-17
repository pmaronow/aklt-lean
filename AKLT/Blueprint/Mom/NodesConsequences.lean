module
public import AKLT.Blueprint.Mom.NodesExact

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.Blueprint.Mom

/-- The conditioning event fixing every site other than `x`. -/
def oneSiteFibre {n : ℕ} (x : Fin n) (σ τ : Fin n → SpinLetter) : Prop :=
  ∀ z, z ≠ x → τ z = σ z

/-- Actual finite conditional spin mean, with its event mass in the denominator.
Probabilistic results below always require that mass to be positive. -/
def conditionalSpinMean {n : ℕ} (p : Weight (Fin n → SpinLetter))
    (x : Fin n) (σ : Fin n → SpinLetter) : Vec3 := by
  classical
  exact fun i =>
    (∑ τ, if oneSiteFibre x σ τ then p τ * spinVector (τ x) i else 0) /
      eventMass p (oneSiteFibre x σ)

/-- `l:35`, lines 290–294: isolate the factors at an unpinned site on a
positive fiber. Enumerate its at most three retained neighbors; the other
factors cancel. Explicit positivity prevents total division at a zero fiber.
This is the paper's conditional-mean consequence, absent from the compact Top type. -/
def OneSiteConditionalReductionStatement : Prop :=
  ∀ n : ℕ, ∀ D : FiniteSpinNetwork n, D.Valid → ∀ pinned : Bool,
    ∀ x : Fin n, D.pinCount x = 0 →
    (D.bonds.filter fun e => e.1 = x ∨ e.2 = x).card ≤ 3 →
    ∀ σ : Fin n → SpinLetter,
    0 < eventMass (normalize (D.weight pinned)) (oneSiteFibre x σ) →
      ∃ k : ℕ, k ≤ 3 ∧ ∃ a : Fin k → Vec3,
        (∀ j, normSq (a j) ≤ 1) ∧ 0 < siteFunctional (D.status x) (localProduct a) ∧
        conditionalSpinMean (normalize (D.weight pinned)) x σ = localMean (D.status x) a

/-- The ten open inputs for moments. Proven constant, antipodality, mixture,
and product-factorization nodes are supplied by Assembly, not requested again. -/
def MomentInputs : Prop :=
  IcoInjectivityStatement ∧ IcoUnitStatement ∧ OddMonomialStatement ∧
  SecondScalarMomentStatement ∧ FourthScalarMomentStatement ∧ MixedScalarMomentStatement ∧
  ScalarTensorReconstructionStatement ∧ TensorMonomialStatement ∧
  OrthogonalTensorStatement ∧ PolynomialExpansionStatement

/-- The seven additional open inputs for finite facts. -/
def FiniteInputs : Prop :=
  BallDotBoundsStatement ∧ LetterAvoidanceStatement ∧ GreedyAssignmentStatement ∧
  FreeCoefficientsStatement ∧ FreeDegreeStatement ∧ TwoSiteFactorizationStatement ∧
  FactorizedConditioningStatement

/-- Thirteen independent closed inputs for the three-factor and covering argument.
The unit-length trigonometric path node is already proved. -/
def MeanInputs : Prop :=
  TripleNormalizerStatement ∧ TripleNumeratorStatement ∧ TripleGeometryStatement ∧
  TripleSOSIdentityStatement ∧ BallFieldSplitStatement ∧ ProductMixtureStatement ∧
  PositiveMixtureEstimateStatement ∧ DepletedContractionStatement ∧
  MeanPathContinuityStatement ∧ MeanPathEndpointsStatement ∧ MeanCovarianceStatement ∧
  OrthogonalNormStatement ∧ OrthogonalTransportStatement

/-- A packaging contract, not an open leaf: all four assigned Top interfaces. -/
def AllTargets : Prop :=
  AKLT.Blueprint.Top.MomentsStatement ∧ AKLT.Blueprint.Top.FiniteFactsStatement ∧
  AKLT.Blueprint.Top.ThreeFactorMeanStatement ∧ AKLT.Blueprint.Top.ExactStatement

end AKLT.Blueprint.Mom
