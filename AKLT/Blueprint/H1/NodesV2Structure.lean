import AKLT.Blueprint.H1.NodesV2Pauli

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs

namespace AKLT.Blueprint.H1

/-- The entire structural conclusion at a fixed matrix, with no positivity claim.
Every clause is real linear in the matrix, including the supported-pair sandwich. -/
def OperatorStructureAtV2 (π : PatternData) (r : Representation)
    (M : Matrix (reductionVectors π r → Fin 2) (reductionVectors π r → Fin 2) ℂ) : Prop :=
  let J := reductionVectors π r
  let O := Matrix.toEuclideanLin M
  M.IsHermitian ∧ (∀ σ τ, (M σ τ).im = 0) ∧
    (∀ g : Matrix (Fin 2) (Fin 2) ℂ, g.conjTranspose * g = 1 → g.det = 1 →
      Commute M (tensorPowerMatrix J g)) ∧
    Commute O (totalSpinZ J) ∧ Commute O (totalSpinPlus J) ∧ Commute O (totalSpinMinus J) ∧
    ∀ x : reductionGroups π, ∀ h : groupIsPair π r x.val = true,
      (π.statusAt x.val = .U →
        let proj := symmetricPairProjection J (leaderToken π r x) (secondToken π r x h)
        O = proj * O * proj) ∧
      (π.statusAt x.val = .D → Commute O (exchangeOperator J (leaderToken π r x) (secondToken π r x h)))

/-- `l:Ostruct`, D.7, lines 320–417; interpolate the real-threshold Pauli matrix
from the two exact rational thresholds 1/3 and 2/3. Linearity of coefficient maps,
inversion and the Pauli map gives the weights 2−3c and 3c−1. No spectral/positivity
statement is interpolated, and no division by a variable is used. -/
def RealDifferencePauliInterpolationStatementV2 : Prop :=
  ∀ π : PatternData, ∀ r : Representation, ∀ I : Finset (Fin 20), ∀ c : ℝ,
    pauliOperatorReal (reductionVectors π r) (invertPolynomialReal I (reducedDifferenceReal π r c)) =
      ((2 - 3 * c : ℝ) : ℂ) •
        pauliOperator (reductionVectors π r) (invertPolynomial I (reducedDifference π r (1 / 3))) +
      ((3 * c - 1 : ℝ) : ℂ) •
        pauliOperator (reductionVectors π r) (invertPolynomial I (reducedDifference π r (2 / 3)))

/-- `l:Ostruct`, D.7; distribute all structural identities over a real linear
combination. Real coefficients preserve Hermiticity/reality. Commutators and
fixed-projection sandwiches are linear; positivity is deliberately absent.
Split the proof into the seven conjunction fields, using matrix-to-End linearity. -/
def OperatorStructureLinearCombinationStatementV2 : Prop :=
  ∀ π : PatternData, ∀ r : Representation,
    ∀ A B : Matrix (reductionVectors π r → Fin 2) (reductionVectors π r → Fin 2) ℂ,
      OperatorStructureAtV2 π r A → OperatorStructureAtV2 π r B → ∀ a b : ℝ,
        OperatorStructureAtV2 π r ((a : ℂ) • A + (b : ℂ) • B)

end AKLT.Blueprint.H1
