module
public import AKLT.Blueprint.Top.Common
public import AKLT.Defs.OperatorContracts
public import AKLT.Defs.RealOperator

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs

namespace AKLT.Blueprint.Top

/-- `l:Iw`: exact passage integration, positive next sum, affine slot polynomials,
and simultaneous orthogonal covariance. Removed-site scalar products are zero. -/
def IntegratePassageStatement : Prop :=
  ∀ π : PatternData, π.Covered →
    (∀ next : Bool, VectorAffine (originalPatternPolynomial π next)) ∧
    (∀ next : Bool, ∀ m : Fin 20 → UnitVector,
      evaluateReduced (originalPatternPolynomial π next) (fun j => (m j).val) =
        if next then patternNext π m else patternCurrent π m) ∧
    (∀ next : Bool, ∀ R : Matrix (Fin 3) (Fin 3) ℝ, R.transpose * R = 1 → ∀ m : Fin 20 → Vec3,
      evaluateReduced (originalPatternPolynomial π next) (fun j => R.mulVec (m j)) =
        evaluateReduced (originalPatternPolynomial π next) m) ∧
    ∀ m : Fin 20 → UnitVector, ∀ f g : Plane,
      ({π.outgoing.step, f, g} : Finset Plane) = {(1, 0), (0, 1), (-1, 0)} →
      π.outgoing.step ≠ f → π.outgoing.step ≠ g → f ≠ g →
      let I := fun n : Plane → Vec3 => 1 +
        (dot (n f) (n g) + dot (n f) (n π.outgoing.step) + dot (n g) (n π.outgoing.step)) / 3
      let J := fun n : Plane → Vec3 => 1 + dot (n f) (n g) / 5
      patternCurrent π m = withoutPassageFunctional π m I ∧
      patternNext π m = withoutPassageFunctional π m J ∧ 0 < patternNext π m ∧
      ∀ c : ℝ, 0 < c → c < 1 →
        patternCurrent π m - c * patternNext π m =
          withoutPassageFunctional π m (fun n => (1 - c) +
            (dot (n f) (n π.outgoing.step) + dot (n g) (n π.outgoing.step)) / 3 +
              (1 / 3 - c / 5) * dot (n f) (n g))

/-- `l:leaf`: positive isolated factors and the three exact one-bond leaf radii,
with a common factor and a vector in the closed unit ball. -/
def LeafStatement : Prop :=
  ∀ π : PatternData, π.Covered → ∀ m : Fin 20 → UnitVector,
    ∀ x ∈ templateCorners ∪ templateTips, π.statusAt x ≠ .X →
      (patternDegree π x = 0 → 0 < siteFunctional (π.statusAt x) (coveredSiteField m x)) ∧
      (patternDegree π x = 1 → ∃ A : ℝ, 0 < A ∧ ∃ u : Vec3, normSq u ≤ 1 ∧
        ∀ v : Vec3, normSq v ≤ 1 →
          siteFunctional (π.statusAt x) (fun n => coveredSiteField m x n * (1 + dot n v)) =
            A * (1 + (replacementRadius π x : ℝ) * dot u v))

/-- Legacy rational specialization of `c:reduce`; use V2 for real thresholds.
Both permitted representations are vector-affine and orthogonally
covariant; each original assignment has the same positive K in current and next. -/
def ReduceStatement : Prop :=
  ∀ π : PatternData, π.Covered → ∀ r : Representation, ∀ c : ℚ, 0 < c → c < 1 →
    VectorAffine (reducedDifference π r c) ∧
    (∀ R : Matrix (Fin 3) (Fin 3) ℝ, R.transpose * R = 1 → ∀ u : Fin 20 → Vec3,
      evaluateReduced (reducedDifference π r c) (fun j => R.mulVec (u j)) =
        evaluateReduced (reducedDifference π r c) u) ∧
    ((∀ u : Fin 20 → UnitVector, 0 ≤ evaluateReduced (reducedDifference π r c) (fun j => (u j).val)) →
      ∀ m : Fin 20 → UnitVector, 0 ≤ patternCurrent π m - (c : ℝ) * patternNext π m) ∧
    ∀ m : Fin 20 → UnitVector, ∃ K : ℝ, 0 < K ∧ ∃ u : Fin 20 → Vec3,
      (∀ j ∈ reductionVectors π r, normSq (u j) ≤ 1) ∧
      patternCurrent π m = K * evaluateReduced (reducedPolynomial π r false) u ∧
      patternNext π m = K * evaluateReduced (reducedPolynomial π r true) u

/-- Legacy rational, twenty-token specialization; `InversionStatementV2`
is the arbitrary-real, arbitrary-finite-vector contract. One supplied
inversion with positive Pauli operator proves positivity on the product of closed balls. -/
def InversionStatement : Prop :=
  (∀ u : Vec3, normSq u ≤ 1 → (spinDensity u).PosSemidef ∧ (spinDensity u).trace = 1) ∧
  ∀ J : Finset (Fin 20), ∀ p : MvPolynomial (Fin 20 × Fin 3) ℚ,
    VectorAffine p → SupportedVectors J p → ∀ I : Finset (Fin 20), I ⊆ J →
    (∀ u : Fin 20 → Vec3, (∀ j ∈ J, normSq (u j) ≤ 1) →
      (evaluateReduced p u : ℂ) =
        (pauliOperator J (invertPolynomial I p) * productDensity J (invertVectors I u)).trace) ∧
    ((pauliOperator J (invertPolynomial I p)).PosSemidef →
      ∀ u : Fin 20 → Vec3, (∀ j ∈ J, normSq (u j) ≤ 1) → 0 ≤ evaluateReduced p u)

/-- Legacy rational-threshold specialization of `l:Ostruct`; use V2 below.
Real symmetric Pauli operators, SU(2), and ladder commutators,
U-pair support and D-pair exchange symmetry, for inversions that are unions of groups. -/
def OperatorStructureStatement : Prop :=
  ∀ π : PatternData, π.Covered → ∀ r : Representation, ∀ I : Finset (Fin 20), GroupInversion π r I →
    ∀ c : ℚ, 0 < c → c < 1 →
    let J := reductionVectors π r
    let M := pauliOperator J (invertPolynomial I (reducedDifference π r c))
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

/-- `l:sector`: ladder detection on each actual supported tensor sector, with inherited
inner product. Only equality of eigenvalue sets is claimed, never multiplicities. -/
def SectorStatement : Prop :=
  ∀ π : PatternData, ∀ r : Representation, ∀ ε : ExchangeSigns π,
    let J := reductionVectors π r
    let S := exchangeSpace π r ε
    let C := centralSpace π r ε
    ∀ O : Module.End ℂ (EuclideanSpace ℂ (J → Fin 2)),
      (∀ ψ ∈ S, O ψ ∈ S) →
      (∀ ψ ∈ S, ∀ χ ∈ S, inner ℂ (O ψ) χ = inner ℂ ψ (O χ)) →
      (∀ ψ ∈ S, O (totalSpinZ J ψ) = totalSpinZ J (O ψ)) →
      (∀ ψ ∈ S, O (totalSpinPlus J ψ) = totalSpinPlus J (O ψ)) →
      (∀ ψ ∈ S, O (totalSpinMinus J ψ) = totalSpinMinus J (O ψ)) →
      (∀ ψ ∈ C, O ψ ∈ C) ∧ eigenvaluesOn C O = eigenvaluesOn S O ∧
        (PositiveOn C O ↔ PositiveOn S O)

/-- `l:gram-residual`: integer diagonal dominance and a positive-semidefinite Gram term
give positive definiteness over both R and C. L need not be invertible. -/
def GramResidualStatement : Prop :=
  ∀ n : ℕ, ∀ M L : Matrix (Fin n) (Fin n) ℤ, M.IsSymm →
    (∀ i j, i < j → L i j = 0) → ∀ g d S : ℕ, GramResidualRows M L g d S →
      ((gramResidual M L g d S).map (Int.castRingHom ℝ)).PosDef ∧
      ((gramResidual M L g d S).map (Int.castRingHom ℂ)).PosDef ∧
      (M.map (Int.castRingHom ℝ)).PosDef ∧ (M.map (Int.castRingHom ℂ)).PosDef

/-- `l:integercheck`: exact reconstruction and positive congruence scale 15D0q;
the optional Bareiss fallback includes integer divisibility and the leading-minor identity. -/
def IntegerCheckStatement : Prop :=
  (∀ π : PatternData, π.Covered → ∀ r : Representation, ∀ I : Finset (Fin 20), GroupInversion π r I →
    ∀ D₀ : ℕ, ClearsDenominator π r D₀ → ∀ p q : ℕ, 0 < p → 0 < q → (p : ℚ) / q < 1 →
    ∀ ε : ExchangeSigns π,
      (∀ next : Bool, (integerSectorMatrix π r ε I D₀ next).IsSymm ∧
        ∀ a b, (integerSectorMatrix π r ε I D₀ next a b : ℚ) =
          (if next then 5 else 3) * (D₀ : ℚ) * rationalSectorEntry π r ε
            (invertPolynomial I (reducedPolynomial π r next)) a b) ∧
      (∀ a b, (thresholdSectorMatrix π r ε I D₀ p q a b : ℂ) =
        (15 * (D₀ : ℂ) * q) * complexSectorMatrix π r ε
          (invertPolynomial I (reducedDifference π r ((p : ℚ) / q))) a b) ∧
      ((complexSectorMatrix π r ε (invertPolynomial I (reducedDifference π r ((p : ℚ) / q)))).PosDef ↔
        ((thresholdSectorMatrix π r ε I D₀ p q).map (Int.castRingHom ℂ)).PosDef)) ∧
  ∀ n : ℕ, ∀ M : Matrix (Fin n) (Fin n) ℤ, M.IsSymm →
    ((M.map (Int.castRingHom ℝ)).PosDef ↔ ∀ k : ℕ, ∀ h : k ≤ n, 0 < k → 0 < leadingMinor M k h) ∧
    ∀ j : ℕ, ∀ h : j < n, (∀ k < j, bareissPivot M k ≠ 0) →
      bareissPivot M j = leadingMinor M (j + 1) (by omega) ∧
      ∀ i l : Fin n, j < i.val → j < l.val →
        (bareissState M j).2 ∣
          (bareissPivot M j * (bareissState M j).1 i l -
            (bareissState M j).1 i ⟨j, h⟩ * (bareissState M j).1 ⟨j, h⟩ l)

/-- `p:certificate`: reconstructed supported sectors and division-free integer witnesses
imply the pointwise local inequality. No stored matrix or pivot is trusted. -/
def CertificateStatement : Prop :=
  ∀ π : PatternData, π.Covered → ∀ r : Representation, ∀ I : Finset (Fin 20), GroupInversion π r I →
    ∀ D₀ : ℕ, ClearsDenominator π r D₀ → ∀ p q : ℕ, 0 < p → 0 < q → (p : ℚ) / q < 1 →
    (∀ ε : ExchangeSigns π, ∃ t : ℕ, ∃ index : Fin t ≃ CentralBasis π r ε, ∃ g d S : ℕ,
      ∃ L : Matrix (Fin t) (Fin t) ℤ,
        (∀ i j, i < j → L i j = 0) ∧ GramResidualRows (indexedSectorMatrix π r ε I D₀ p q index) L g d S) →
      ∀ m : Fin 20 → UnitVector, 0 ≤ patternCurrent π m - ((p : ℝ) / q) * patternNext π m

/-- Corrected full real scope of `c:reduce`.
The rational specialization is retained for existing proved blueprint assemblies. -/
def ReduceStatementV2 : Prop :=
  ∀ π : PatternData, π.Covered → ∀ r : Representation, ∀ c : ℝ, 0 < c → c < 1 →
    VectorAffineReal (reducedDifferenceReal π r c) ∧
    (∀ R : Matrix (Fin 3) (Fin 3) ℝ, R.transpose * R = 1 → ∀ u : Fin 20 → Vec3,
      evaluateRealPolynomial (reducedDifferenceReal π r c) (fun j => R.mulVec (u j)) =
        evaluateRealPolynomial (reducedDifferenceReal π r c) u) ∧
    ((∀ u : Fin 20 → UnitVector, 0 ≤ evaluateRealPolynomial (reducedDifferenceReal π r c) (fun j => (u j).val)) →
      ∀ m : Fin 20 → UnitVector, 0 ≤ patternCurrent π m - (c : ℝ) * patternNext π m) ∧
    ∀ m : Fin 20 → UnitVector, ∃ K : ℝ, 0 < K ∧ ∃ u : Fin 20 → Vec3,
      (∀ j ∈ reductionVectors π r, normSq (u j) ≤ 1) ∧
      patternCurrent π m = K * evaluateReduced (reducedPolynomial π r false) u ∧
      patternNext π m = K * evaluateReduced (reducedPolynomial π r true) u

/-- Corrected full real scope of `l:inversion`.
The rational specialization is retained for existing proved blueprint assemblies. -/
def InversionStatementV2 : Prop :=
  (∀ u : Vec3, normSq u ≤ 1 → (spinDensity u).PosSemidef ∧ (spinDensity u).trace = 1) ∧
  ∀ n : ℕ, ∀ J : Finset (Fin n), ∀ p : RealVectorPolynomial n,
    VectorAffineReal p → SupportedVectorsReal J p → ∀ I : Finset (Fin n), I ⊆ J →
    (∀ u : Fin n → Vec3, (∀ j ∈ J, normSq (u j) ≤ 1) →
      (evaluateRealPolynomial p u : ℂ) =
        (pauliOperatorReal J (invertPolynomialReal I p) * productDensityReal J (invertVectorsReal I u)).trace) ∧
    ((pauliOperatorReal J (invertPolynomialReal I p)).PosSemidef →
      ∀ u : Fin n → Vec3, (∀ j ∈ J, normSq (u j) ≤ 1) → 0 ≤ evaluateRealPolynomial p u)

/-- Corrected full real scope of `l:Ostruct`.
The rational specialization is retained for existing proved blueprint assemblies. -/
def OperatorStructureStatementV2 : Prop :=
  ∀ π : PatternData, π.Covered → ∀ r : Representation, ∀ I : Finset (Fin 20), GroupInversion π r I →
    ∀ c : ℝ, 0 < c → c < 1 →
    let J := reductionVectors π r
    let M := pauliOperatorReal J (invertPolynomialReal I (reducedDifferenceReal π r c))
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

/-- `t:H1`: the missing finite-data handoff. Every covered pattern must actually
admit a representation, group inversion, justified denominator, and reconstructed
Gram witnesses at its fixed threshold. A soundness implication alone supplies none
of these witnesses. This is an unproved finite certificate obligation. -/
def H1FiniteDataStatementV2 : Prop :=
  ∀ π : PatternData, π.Covered → ∃ r : Representation, ∃ I : Finset (Fin 20),
    GroupInversion π r I ∧ ∃ D₀ : ℕ, ClearsDenominator π r D₀ ∧
      H1SectorWitnesses π r I D₀ (h1Numerator π) (h1Denominator π)

/-- Combined `p:certificate` soundness and `t:H1` finite-data existence.
The original `CertificateStatement` retains its valid conditional meaning. -/
def CertificateStatementV2 : Prop := CertificateStatement ∧ H1FiniteDataStatementV2

end AKLT.Blueprint.Top
