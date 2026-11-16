import AKLT.Blueprint.H1.NodesPauli

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs

namespace AKLT.Blueprint.H1

/-- `d:Pauli`/`l:Ostruct`, lines 266–270 and 350–357; tensor products of
Hermitian Pauli factors are Hermitian and all rational coefficients are real. -/
def PauliHermitianStatement : Prop :=
  ∀ J : Finset (Fin 20), ∀ p : VectorPolynomial, (pauliOperator J p).IsHermitian

/-- `l:Ostruct`, lines 350–357; reflect the second coordinate and compare real
polynomial coefficients. Odd numbers of sigma_2 factors have zero coefficient. -/
def ReflectionParityStatement : Prop :=
  ∀ J : Finset (Fin 20), ∀ p : VectorPolynomial, VectorAffine p → SupportedVectors J p →
    OrthogonalInvariant p → ∀ a : J → Fin 4, Odd (pauliYCount J a) → p.coeff (pauliExponent J a) = 0

/-- `l:Ostruct`, lines 350–357; even sigma_2 products have real entries and odd
ones have zero coefficients. This step is purely finite Pauli arithmetic. -/
def PauliRealityStatement : Prop :=
  ∀ J : Finset (Fin 20), ∀ p : VectorPolynomial,
    (∀ a : J → Fin 4, Odd (pauliYCount J a) → p.coeff (pauliExponent J a) = 0) →
    ∀ σ τ, (pauliOperator J p σ τ).im = 0

/-- `l:Ostruct`, lines 348–350; tokenwise signs commute with real linear
rotations. Establish evaluation/substitution compatibility, then substitute. -/
def InversionCovarianceStatement : Prop :=
  ∀ p : VectorPolynomial, OrthogonalInvariant p → ∀ I : Finset (Fin 20),
    OrthogonalInvariant (invertPolynomial I p)

/-- `l:Ostruct`, lines 359–367; expand conjugated traceless Hermitian 2×2
matrices in the real Pauli basis. Use entry coordinates or half-trace pairings. -/
def AdjointPauliCoordinatesStatement : Prop :=
  ∀ g : Matrix (Fin 2) (Fin 2) ℂ, g.conjTranspose * g = 1 → g.det = 1 →
    ∃ R : Matrix (Fin 3) (Fin 3) ℝ, ∀ j : Fin 3,
      g * pauli ⟨j.val + 1, by omega⟩ * g.conjTranspose =
        ∑ l : Fin 3, (R l j : ℂ) • pauli ⟨l.val + 1, by omega⟩

/-- `l:Ostruct`, lines 359–369; conjugation preserves the half-trace pairing.
Insert the Pauli expansion and use Tr(sigma_i sigma_j)=2 delta_ij. -/
def AdjointPauliOrthogonalStatement : Prop :=
  ∀ g : Matrix (Fin 2) (Fin 2) ℂ, g.conjTranspose * g = 1 →
    ∀ R : Matrix (Fin 3) (Fin 3) ℝ,
      (∀ j : Fin 3, g * pauli ⟨j.val + 1, by omega⟩ * g.conjTranspose =
        ∑ l : Fin 3, (R l j : ℂ) • pauli ⟨l.val + 1, by omega⟩) → R.transpose * R = 1

/-- `l:Ostruct`, lines 368–377; expand tensor conjugation using the supplied
adjoint coordinates. Covariance of the polynomial gives commutation after
cancelling the unitary tensor power. No spin representation theorem is assumed. -/
def PauliRotationTransferStatement : Prop :=
  ∀ J : Finset (Fin 20), ∀ p : VectorPolynomial, VectorAffine p → SupportedVectors J p →
    OrthogonalInvariant p → ∀ g : Matrix (Fin 2) (Fin 2) ℂ, g.conjTranspose * g = 1 →
    ∀ R : Matrix (Fin 3) (Fin 3) ℝ, R.transpose * R = 1 →
      (∀ j : Fin 3, g * pauli ⟨j.val + 1, by omega⟩ * g.conjTranspose =
        ∑ l : Fin 3, (R l j : ℂ) • pauli ⟨l.val + 1, by omega⟩) →
      Commute (pauliOperator J p) (tensorPowerMatrix J g)

/-- `l:Ostruct`, lines 379–389; normalize I-it sigma_j to an SU(2) matrix,
then clear the positive denominator from its tensor power. -/
def CayleyTensorCommutationStatement : Prop :=
  ∀ J : Finset (Fin 20), ∀ M : Matrix (J → Fin 2) (J → Fin 2) ℂ,
    (∀ g : Matrix (Fin 2) (Fin 2) ℂ, g.conjTranspose * g = 1 → g.det = 1 →
      Commute M (tensorPowerMatrix J g)) →
    ∀ j : Fin 3, ∀ t : ℝ,
      Commute M (tensorPowerMatrix J (1 + (t : ℂ) • (-Complex.I • pauli ⟨j.val + 1, by omega⟩)))

/-- `l:Ostruct`, lines 386–394; compare the degree-one coefficient of a matrix
polynomial vanishing at every real t. Its coefficient is the sum of token lifts. -/
def TensorLinearCoefficientStatement : Prop :=
  ∀ J : Finset (Fin 20), ∀ M : Matrix (J → Fin 2) (J → Fin 2) ℂ,
    ∀ A : Matrix (Fin 2) (Fin 2) ℂ,
      (∀ t : ℝ, Commute M (tensorPowerMatrix J (1 + (t : ℂ) • A))) →
      Commute M (∑ j : J, tokenMatrix J j A)

/-- `l:Ostruct`, lines 390–394; cancel -i and take the linear combinations
defining the three total spin maps. The empty tensor has zero generators. -/
def SpinGeneratorTransferStatement : Prop :=
  ∀ J : Finset (Fin 20), ∀ M : Matrix (J → Fin 2) (J → Fin 2) ℂ,
    (∀ k : Fin 3, Commute M (∑ j : J, tokenMatrix J j (-Complex.I • pauli ⟨k.val + 1, by omega⟩))) →
    Commute (Matrix.toEuclideanLin M) (totalSpinZ J) ∧
    Commute (Matrix.toEuclideanLin M) (totalSpinPlus J) ∧
    Commute (Matrix.toEuclideanLin M) (totalSpinMinus J)

/-- `l:Ostruct`, lines 397–412; finite moments commute with Pauli coefficient
extraction and inversion. Expand one monomial, then interchange the finite sums.
This isolates the generic moment/Pauli bridge from the corner combinatorics. -/
def MomentPauliInterchangeStatement : Prop :=
  MonomialMoments → ∀ V : Finset Plane, ∀ s : Plane → Status,
    (∀ x ∈ V, s x = .U ∨ s x = .D) → ∀ p : LocalPolynomial,
    InternalAdmissible V p → ∀ J I : Finset (Fin 20),
      pauliOperator J (invertPolynomial I (contractSpins V s p)) = rawPauliFunctional V s J I p

/-- `l:Ostruct`, lines 397–431; pull the two equal-sign slot factors out of the
real Pauli polynomial in every raw summand. The remaining factors have disjoint
tokens, hence commute with pair symmetries. Remove zero-weight U atoms. Current
and next may be enumerated separately and joined with signed coefficients. -/
def PairExpansionFromRealizationStatement : Prop :=
  (∀ j : IcoLetter, normSq (icoVector j) = 1) →
  ∀ π : PatternData, π.Covered → ∀ r : Representation,
    ∀ I : Finset (Fin 20), GroupInversion π r I →
    (∀ next : Bool, pauliOperator (reductionVectors π r) (invertPolynomial I (reducedPolynomial π r next)) =
      rawPauliFunctional (reducedSpinSites π r) (nextStatus π next) (reductionVectors π r) I
        (reducedIntegrand π r next)) →
    ∀ c : ℚ, ∀ x : reductionGroups π, ∀ h : groupIsPair π r x.val = true,
      PairExpansion (reductionVectors π r) (leaderToken π r x) (secondToken π r x h)
        (Matrix.toEuclideanLin (pauliOperator (reductionVectors π r)
          (invertPolynomial I (reducedDifference π r c)))) (π.statusAt x.val = .U)

/-- Assembled `l:Ostruct` intermediate, proved in Assembly from generic
moment/Pauli interchange and the explicit pair-factor realization. -/
def RetainedPairExpansionStatement : Prop :=
  MonomialMoments → (∀ j : IcoLetter, normSq (icoVector j) = 1) →
  ∀ π : PatternData, π.Covered → ∀ r : Representation,
    (∀ next : Bool, InternalAdmissible (reducedSpinSites π r) (reducedIntegrand π r next)) →
    ∀ I : Finset (Fin 20), GroupInversion π r I → ∀ c : ℚ,
    ∀ x : reductionGroups π, ∀ h : groupIsPair π r x.val = true,
      PairExpansion (reductionVectors π r) (leaderToken π r x) (secondToken π r x h)
        (Matrix.toEuclideanLin (pauliOperator (reductionVectors π r)
          (invertPolynomial I (reducedDifference π r c)))) (π.statusAt x.val = .U)

/-- `l:Ostruct`, lines 413–423; for unit n, I+eta n.sigma has rank one.
Its tensor square is fixed on both sides by the symmetric projection. -/
def UnitPairSupportStatement : Prop :=
  ∀ J : Finset (Fin 20), ∀ j k : J, j ≠ k → ∀ η : ℝ, η ^ 2 = 1 →
    ∀ n : Vec3, normSq n = 1 →
      symmetricPairProjection J j k * pairTerm J j k η n = pairTerm J j k η n ∧
      pairTerm J j k η n * symmetricPairProjection J j k = pairTerm J j k η n

/-- `l:Ostruct`, lines 425–431; swapping equal factors commutes with their
tensor product, including n=0. No unit or sign assumption is needed. -/
def EqualPairExchangeStatement : Prop :=
  ∀ J : Finset (Fin 20), ∀ j k : J, ∀ η : ℝ, ∀ n : Vec3,
    Commute (pairTerm J j k η n) (exchangeOperator J j k)

/-- `l:Ostruct`, lines 411–431; distribute pair support and exchange over a
finite expansion. The auxiliary factors' commutation is an explicit premise. -/
def PairExpansionTransferStatement : Prop :=
  ∀ J : Finset (Fin 20), ∀ j k : J, ∀ O : Module.End ℂ (TensorSpace J), ∀ unitOnly : Prop,
    PairExpansion J j k O unitOnly →
    (∀ η : ℝ, η ^ 2 = 1 → ∀ n : Vec3, normSq n = 1 →
      symmetricPairProjection J j k * pairTerm J j k η n = pairTerm J j k η n ∧
      pairTerm J j k η n * symmetricPairProjection J j k = pairTerm J j k η n) →
    (∀ η : ℝ, ∀ n : Vec3, Commute (pairTerm J j k η n) (exchangeOperator J j k)) →
    (unitOnly → O = symmetricPairProjection J j k * O * symmetricPairProjection J j k) ∧
    Commute O (exchangeOperator J j k)

/-- The totalized group indices are still distinct: leader is at most 17 and
second is its successor. Thus no pair operation accidentally exchanges one token. -/
def PairTokensDistinctStatement : Prop :=
  ∀ π : PatternData, ∀ r : Representation, ∀ x : reductionGroups π,
    ∀ h : groupIsPair π r x.val = true, leaderToken π r x ≠ secondToken π r x h

theorem pairTokensDistinct : PairTokensDistinctStatement := by
  intro π r x h hEqual
  have hBound : (groupLeader x.val).val < 19 := by
    unfold groupLeader
    split_ifs <;> norm_num
  have hValue := congrArg (fun j : reductionVectors π r => j.val.val) hEqual
  change (groupLeader x.val).val = min 19 ((groupLeader x.val).val + 1) at hValue
  omega

end AKLT.Blueprint.H1
