module
public import AKLT.Blueprint.H1.NodesLeaf

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs

namespace AKLT.Blueprint.H1

/-- `c:reduce`, lines 198–214; count factors after each allowed leaf deletion.
The passage is retained in the existing Defs integrand; its three/two bonds
have degrees three/two, giving the same contraction as passage-first integration. -/
def ReducedDegreeStatement : Prop :=
  ∀ π : PatternData, π.Covered → ∀ r : Representation, ∀ next : Bool,
    InternalAdmissible (reducedSpinSites π r) (reducedIntegrand π r next)

/-- `c:reduce`, lines 198–214; disjoint groups give separate vector affineness,
all factors are scalar products, and each token lies in `reductionVectors`. -/
def ReducedFactorStructureStatement : Prop :=
  ∀ π : PatternData, π.Covered → ∀ r : Representation, ∀ next : Bool,
    LocalVectorAffine (reducedIntegrand π r next) ∧
    IntegrandInvariant (reducedIntegrand π r next) ∧
    LocalSupportedVectors (reductionVectors π r) (reducedIntegrand π r next)

/-- `c:reduce`, lines 217–222; no two peripheral sites are nearest neighbors.
Enumerate the template and both deletion rules; any deleted bonded leaf has its
unique neighbor in the retained spin set. -/
def PeripheralGeometryStatement : Prop :=
  ∀ π : PatternData, π.Covered → ∀ r : Representation, PeripheralGeometry π r

/-- `c:reduce`, lines 217–229; use the disjoint-union equivalence between spin
assignments on retained/deleted sets, and factor the deleted finite sums.
This leaf handles Fubini only, with no choice of replacement vectors. -/
def PeripheralFubiniStatement : Prop :=
  ∀ π : PatternData, π.Covered → ∀ r : Representation, PeripheralGeometry π r →
    ∀ next : Bool, ∀ m : Fin 20 → UnitVector,
      (if next then patternNext π m else patternCurrent π m) = separatedLeafFunctional π r next m

/-- `c:reduce`, lines 222–237; choose the local normalizers and replacement
vectors once, before next is quantified. Factor their finite product K out of
the separated sum. Unused tokens are zero; an empty product gives K=1. -/
def PeripheralAssignmentStatement : Prop :=
  (∀ j : IcoLetter, normSq (icoVector j) = 1) →
  ∀ π : PatternData, π.Covered → ∀ r : Representation, PeripheralGeometry π r →
    ∀ m : Fin 20 → UnitVector, LeafRule π m →
      ∃ K : ℝ, 0 < K ∧ ∃ u : Fin 20 → Vec3, (∀ j, normSq (u j) ≤ 1) ∧
        ∀ next : Bool, separatedLeafFunctional π r next m = K *
          rawFunctional (reducedSpinSites π r) (nextStatus π next) (reducedIntegrand π r next) u

/-- Assembled `c:reduce` intermediate: the SAME positive factor and SAME vectors
for current and next, with all twenty vector norms bounded. Proved in Assembly
from the three preceding smaller leaves and exact moment evaluation. -/
def SimultaneousLeafReconstructionStatement : Prop :=
  (∀ j : IcoLetter, normSq (icoVector j) = 1) →
  ∀ π : PatternData, π.Covered → ∀ r : Representation,
    (∀ next : Bool, ∀ u : Fin 20 → Vec3,
      evaluateReduced (reducedPolynomial π r next) u =
        rawFunctional (reducedSpinSites π r) (nextStatus π next) (reducedIntegrand π r next) u) →
    ∀ m : Fin 20 → UnitVector, LeafRule π m →
      ∃ K : ℝ, 0 < K ∧ ∃ u : Fin 20 → Vec3,
        (∀ j, normSq (u j) ≤ 1) ∧
        patternCurrent π m = K * evaluateReduced (reducedPolynomial π r false) u ∧
        patternNext π m = K * evaluateReduced (reducedPolynomial π r true) u

/-- `c:reduce`, lines 239–247; every ball vector is a convex combination of two
antipodal unit vectors. Branch at zero before division by its norm. -/
def BallChordStatement : Prop := ∀ v : Vec3, normSq v ≤ 1 → UnitChord v

/-- `c:reduce`, lines 242–247; group polynomial monomials by the single coordinate
of token j. `VectorAffine` is stronger than scalar-coordinate multiaffineness. -/
def AffineEvaluationStatement : Prop :=
  ∀ p : VectorPolynomial, VectorAffine p → SeparatelyAffine (evaluateReduced p)

/-- `c:reduce`, lines 242–247; induct over the finite set of non-unit coordinates.
All 20 coordinates are quantified, including unused ones. No minimum or compactness
argument is needed; a zero coefficient in the convex combination is harmless. -/
def ProductBallNonnegativeStatement : Prop :=
  (∀ v : Vec3, normSq v ≤ 1 → UnitChord v) →
  ∀ F : (Fin 20 → Vec3) → ℝ, SeparatelyAffine F →
    (∀ u : Fin 20 → UnitVector, 0 ≤ F (fun j => (u j).val)) →
    ∀ u : Fin 20 → Vec3, (∀ j, normSq (u j) ≤ 1) → 0 ≤ F u

/-- `c:reduce`, lines 198–201; rational scalar combinations preserve all three
structural predicates. This is support inclusion for sums, not equality of supports. -/
def DifferenceStructureStatement : Prop :=
  ∀ J : Finset (Fin 20), ∀ p q : VectorPolynomial, ∀ c : ℚ,
    VectorAffine p → VectorAffine q → OrthogonalInvariant p → OrthogonalInvariant q →
    SupportedVectors J p → SupportedVectors J q →
      VectorAffine (p - MvPolynomial.C c * q) ∧
      OrthogonalInvariant (p - MvPolynomial.C c * q) ∧
      SupportedVectors J (p - MvPolynomial.C c * q)

/-- Assembled intermediate, proved in Assembly from the contraction nodes. -/
def ReducedStructureStatement : Prop :=
  ∀ π : PatternData, π.Covered → ∀ r : Representation, ∀ c : ℚ,
    VectorAffine (reducedDifference π r c) ∧ OrthogonalInvariant (reducedDifference π r c) ∧
      SupportedVectors (reductionVectors π r) (reducedDifference π r c)

/-- `c:reduce`, line 233; evaluation respects subtraction and the rational cast. -/
def DifferenceEvaluationStatement : Prop :=
  ∀ π : PatternData, ∀ r : Representation, ∀ c : ℚ, ∀ u : Fin 20 → Vec3,
    evaluateReduced (reducedDifference π r c) u =
      evaluateReduced (reducedPolynomial π r false) u -
        (c : ℝ) * evaluateReduced (reducedPolynomial π r true) u

theorem differenceEvaluation : DifferenceEvaluationStatement := by
  intro π r c u
  simp [evaluateReduced, reducedDifference]

theorem reducedStatuses (π : PatternData) (r : Representation) (next : Bool)
    (x : Plane) (hx : x ∈ reducedSpinSites π r) :
    nextStatus π next x = .U ∨ nextStatus π next x = .D := by
  classical
  exact activeStatuses π next x (Finset.mem_filter.mp hx).1

end AKLT.Blueprint.H1
