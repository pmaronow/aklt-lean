# BP_MOM declaration signatures

All names below are in `AKLT.Blueprint.Mom`. Every open node is a closed proposition; no named blueprint proposition occurs as a premise inside another leaf. Helper definitions are documented in their linked source modules.

## Open nodes

```lean
def IcoInjectivityStatement : Prop := Function.Injective icoVector
```

```lean
def IcoUnitStatement : Prop := ∀ j, normSq (icoVector j) = 1
```

```lean
def OddMonomialStatement : Prop :=
  ∀ m : Fin 3 → ℕ, (∃ i, Odd (m i)) → moment (mono m) = 0
```

```lean
def SecondScalarMomentStatement : Prop :=
  ∀ i, moment (fun v => v i ^ 2) = 1 / 3
```

```lean
def FourthScalarMomentStatement : Prop :=
  ∀ i, moment (fun v => v i ^ 4) = 1 / 5
```

```lean
def MixedScalarMomentStatement : Prop :=
  ∀ i j, i ≠ j → moment (fun v => v i ^ 2 * v j ^ 2) = 1 / 15
```

```lean
def ScalarTensorReconstructionStatement : Prop :=
  ∀ L : (Vec3 → ℝ) → ℝ,
    L (fun _ => 1) = 1 →
    (∀ m : Fin 3 → ℕ, (∃ i, Odd (m i)) → L (mono m) = 0) →
    (∀ i, L (fun v => v i ^ 2) = 1 / 3) →
    (∀ i, L (fun v => v i ^ 4) = 1 / 5) →
    (∀ i j, i ≠ j → L (fun v => v i ^ 2 * v j ^ 2) = 1 / 15) →
    TensorLaw L 1
```

```lean
def TensorMonomialStatement : Prop :=
  ∀ L : (Vec3 → ℝ) → ℝ, ∀ c : ℝ, TensorLaw L c →
    ∀ m : Fin 3 → ℕ, (∑ i, m i) ≤ 4 → L (mono m) = scaledMoment c m
```

```lean
def OrthogonalTensorStatement : Prop :=
  ∀ (α : Type) [Fintype α], ∀ w : α → ℝ, ∀ v : α → Vec3, ∀ c : ℝ,
    TensorLaw (finiteFunctional w v) c →
    ∀ R : Matrix (Fin 3) (Fin 3) ℝ, R.transpose * R = 1 →
      TensorLaw (finiteFunctional w (fun a => R.mulVec (v a))) c
```

```lean
def PolynomialExpansionStatement : Prop :=
  ∀ n : ℕ, ∀ (α : Fin n → Type) [∀ x, Fintype (α x)],
    ∀ w : (x : Fin n) → α x → ℝ, ∀ v : (x : Fin n) → α x → Vec3,
    ∀ p : MvPolynomial (Fin n × Fin 3) ℝ,
      productSum α w v (fun a => MvPolynomial.eval (fun z => a z.1 z.2) p) =
        ∑ m ∈ p.support, p.coeff m *
          productSum α w v (fun a => ∏ x, mono (fun i => m (x, i)) (a x))
```

```lean
def BallDotBoundsStatement : Prop :=
  ∀ a b : Vec3, normSq a ≤ 1 → normSq b ≤ 1 →
    0 ≤ 1 + dot a b ∧ 1 + dot a b ≤ 2
```

```lean
def LetterAvoidanceStatement : Prop :=
  ∀ k : ℕ, k ≤ 4 → ∀ b : Fin k → Vec3, (∀ i, normSq (b i) ≤ 1) →
    ∃ j : IcoLetter, ∀ i, 0 < 1 + dot (icoVector j) (b i)
```

```lean
def GreedyAssignmentStatement : Prop :=
  ∀ (α : Type) [Fintype α], ∀ v : α → Vec3, (∀ a, normSq (v a) ≤ 1) →
    (∀ k : ℕ, k ≤ 4 → ∀ b : Fin k → Vec3, (∀ i, normSq (b i) ≤ 1) →
      ∃ a, ∀ i, 0 < 1 + dot (v a) (b i)) →
    ∀ n : ℕ, ∀ D : FiniteSpinNetwork n, D.Valid →
      ∃ σ : Fin n → α,
        (∀ e ∈ D.bonds, 0 < 1 + dot (v (σ e.1)) (v (σ e.2))) ∧
        ∀ x, ∀ j : Fin (D.pinCount x), 0 < 1 + dot (D.pin x j).val (v (σ x))
```

```lean
def FreeCoefficientsStatement : Prop :=
  ∀ n : ℕ, ∀ D : FiniteSpinNetwork n, ∀ pairs : List (Fin n × Fin n),
    ∀ m, 0 ≤ (freePolynomial D pairs).coeff m
```

```lean
def FreeDegreeStatement : Prop :=
  ∀ n : ℕ, ∀ D : FiniteSpinNetwork n, D.Valid →
    ∀ pairs : List (Fin n × Fin n),
      (∀ x, (D.bonds.filter fun e => e.1 = x ∨ e.2 = x).card +
        (pairs.filter fun e => e.1 = x).length +
        (pairs.filter fun e => e.2 = x).length ≤ 4) →
      SeparateDegreeFour (freePolynomial D pairs)
```

```lean
def TwoSiteFactorizationStatement : Prop :=
  ∀ n : ℕ, ∀ D : FiniteSpinNetwork n, D.Valid → ∀ pinned : Bool,
    ∀ x y : Fin n, x ≠ y → (x, y) ∉ D.bonds → (y, x) ∉ D.bonds →
    ∀ σ : Fin n → SpinLetter,
      ∃ C : ℝ, ∃ u v : SpinLetter → ℝ,
        0 ≤ C ∧ (∀ a, 0 ≤ u a) ∧ (∀ b, 0 ≤ v b) ∧
        ∀ τ, twoSiteFibre x y σ τ → D.weight pinned τ = C * u (τ x) * v (τ y)
```

```lean
def FactorizedConditioningStatement : Prop :=
  ∀ n : ℕ, ∀ w : (Fin n → SpinLetter) → ℝ, (∀ τ, 0 ≤ w τ) →
    ∀ x y : Fin n, x ≠ y → ∀ σ : Fin n → SpinLetter,
    ∀ C : ℝ, ∀ u v : SpinLetter → ℝ,
    (∀ τ, twoSiteFibre x y σ τ → w τ = C * u (τ x) * v (τ y)) →
    0 < eventMass (normalize w) (twoSiteFibre x y σ) →
    ∀ a b : SpinLetter,
      conditionalProbability (normalize w) (twoSiteFibre x y σ)
        (fun τ => τ x = a ∧ τ y = b) =
      conditionalProbability (normalize w) (twoSiteFibre x y σ) (fun τ => τ x = a) *
        conditionalProbability (normalize w) (twoSiteFibre x y σ) (fun τ => τ y = b)
```

```lean
def TripleNormalizerStatement : Prop :=
  ∀ a : Fin 3 → Vec3, siteFunctional .U (localProduct a) = 1 + tripleP a / 3
```

```lean
def TripleNumeratorStatement : Prop :=
  ∀ a : Fin 3 → Vec3, ∀ i,
    15 * siteFunctional .U (fun v => v i * localProduct a v) = tripleV a i
```

```lean
def TripleGeometryStatement : Prop :=
  ∀ a : Fin 3 → Vec3, (∀ j, normSq (a j) = 1) →
    1 / 2 ≤ 1 + tripleP a / 3 ∧
    0 ≤ 1 - dot (a 1) (a 2) ∧ 0 ≤ 1 - dot (a 0) (a 2) ∧
    0 ≤ 1 - dot (a 0) (a 1)
```

```lean
def TripleSOSIdentityStatement : Prop :=
  ∀ a : Fin 3 → Vec3, (∀ j, normSq (a j) = 1) →
    (9 + 3 * tripleP a)^2 - normSq (tripleV a) = tripleSOS a
```

```lean
def BallFieldSplitStatement : Prop :=
  ∀ a : Vec3, normSq a ≤ 1 → ∃ t : ℝ, ∃ e : UnitVector,
    0 ≤ t ∧ t ≤ 1 ∧
    ∀ v : Vec3, 1 + dot v a =
      t * (1 + dot v e.val) + (1 - t) * (1 + dot v (-e.val))
```

```lean
def ProductMixtureStatement : Prop :=
  ∀ k : ℕ, k ≤ 3 → ∀ a : Fin k → Vec3,
    (∀ j, ∃ t : ℝ, ∃ e : UnitVector, 0 ≤ t ∧ t ≤ 1 ∧
      ∀ v : Vec3, 1 + dot v (a j) =
        t * (1 + dot v e.val) + (1 - t) * (1 + dot v (-e.val))) →
    ∃ t : Fin 8 → ℝ, ∃ b : Fin 8 → Fin 3 → UnitVector,
      (∀ η, 0 ≤ t η) ∧ (∑ η, t η) = 1 ∧
      ∀ v, localProduct a v =
        ∑ η, t η * localProduct (fun j => (b η j).val) v
```

```lean
def PositiveMixtureEstimateStatement : Prop :=
  ∀ (α : Type) [Fintype α], ∀ t A : α → ℝ, ∀ B : α → Vec3, ∀ r : ℝ,
    0 ≤ r → (∀ η, 0 ≤ t η) → (∑ η, t η) = 1 →
    (∀ η, 1 / 2 ≤ A η) →
    (∀ η, normSq (fun i => B η i / A η) ≤ r^2) →
      1 / 2 ≤ ∑ η, t η * A η ∧
      normSq (fun i => (∑ η, t η * B η i) / (∑ η, t η * A η)) ≤ r^2
```

```lean
def DepletedContractionStatement : Prop :=
  ∀ k : ℕ, ∀ a : Fin k → Vec3, 0 < siteFunctional .U (localProduct a) →
    0 < siteFunctional .D (localProduct a) ∧
      normSq (localMean .D a) ≤ normSq (localMean .U a)
```

```lean
def MeanPathContinuityStatement : Prop :=
  ContinuousOn (fun t => normSq (localMean .U (meanPath t))) (Set.Icc 0 meanPathEnd)
```

```lean
def MeanPathEndpointsStatement : Prop :=
  normSq (localMean .U (meanPath 0)) = (3 / 5 : ℝ)^2 ∧
    normSq (localMean .U (meanPath meanPathEnd)) = 0
```

```lean
def MeanCovarianceStatement : Prop :=
  ∀ a : Fin 3 → Vec3, (∀ j, normSq (a j) = 1) →
    ∀ R : Matrix (Fin 3) (Fin 3) ℝ, R.transpose * R = 1 →
      localMean .U (fun j => R.mulVec (a j)) = R.mulVec (localMean .U a)
```

```lean
def OrthogonalNormStatement : Prop :=
  ∀ R : Matrix (Fin 3) (Fin 3) ℝ, R.transpose * R = 1 →
    ∀ v : Vec3, normSq (R.mulVec v) = normSq v
```

```lean
def OrthogonalTransportStatement : Prop :=
  ∀ v w : Vec3, normSq v = normSq w →
    ∃ R : Matrix (Fin 3) (Fin 3) ℝ, R.transpose * R = 1 ∧ R.mulVec v = w
```

```lean
def SingleSiteQuadratureStatement : Prop :=
  ∀ k : ℕ, ∀ F : FrameData k, MomentLaw F →
    ∀ s : Status, s = .U ∨ s = .D →
    ∀ m : Fin 3 → ℕ, (∑ i, m i) ≤ 4 →
      momentLawFunctional F s (mono m) = siteFunctional s (mono m)
```

```lean
def InteractionDegreeStatement : Prop :=
  ∀ n : ℕ, ∀ bonds : List ((Fin n × Fin n) × ℝ),
    ∀ pins : List ((Fin n × Vec3) × ℝ), ∀ p : MvPolynomial (Fin n × Fin 3) ℝ,
    (∀ m ∈ p.support, ∀ x : Fin n,
      (∑ i : Fin 3, m (x, i)) + interactionOccurrences bonds pins x ≤ 4) →
      SeparateDegreeFour (interactionPolynomial bonds pins p)
```

```lean
def OneSiteConditionalReductionStatement : Prop :=
  ∀ n : ℕ, ∀ D : FiniteSpinNetwork n, D.Valid → ∀ pinned : Bool,
    ∀ x : Fin n, D.pinCount x = 0 →
    (D.bonds.filter fun e => e.1 = x ∨ e.2 = x).card ≤ 3 →
    ∀ σ : Fin n → SpinLetter,
    0 < eventMass (normalize (D.weight pinned)) (oneSiteFibre x σ) →
      ∃ k : ℕ, k ≤ 3 ∧ ∃ a : Fin k → Vec3,
        (∀ j, normSq (a j) ≤ 1) ∧ 0 < siteFunctional (D.status x) (localProduct a) ∧
        conditionalSpinMean (normalize (D.weight pinned)) x σ = localMean (D.status x) a
```

## Proven leaf statements

These ten proofs predate the new author rule and are retained. Every future leaf proof first attempt belongs to a different, cheaper model; see `proof-policy.json`.

```lean
def EmptyPartitionStatement : Prop :=
  ∀ D : FiniteSpinNetwork 0, ∀ pinned : Bool, D.partition pinned (fun _ => 1) = 1
theorem emptyPartition : EmptyPartitionStatement
```

```lean
def FrameOptionSumStatement : Prop :=
  ∀ k : ℕ, ∀ F : FrameData k, ∀ s : Status, s = .U ∨ s = .D →
    ∀ f : Vec3 → ℝ,
      finiteFunctional (frameWeight F s) (frameAtom F) f = momentLawFunctional F s f
theorem frameOptionSum : FrameOptionSumStatement
```

```lean
def FreeEvaluationStatement : Prop :=
  ∀ n : ℕ, ∀ D : FiniteSpinNetwork n, ∀ pairs : List (Fin n × Fin n),
    D.partition false (fun a => (pairs.map fun e => dot (a e.1) (a e.2)).prod) =
      productFunctional D.status
        (fun a => MvPolynomial.eval (fun z => a z.1 z.2) (freePolynomial D pairs))
theorem freeEvaluation : FreeEvaluationStatement
```

```lean
def IcoAntipodalStatement : Prop := ∀ j, ∃ k, icoVector k = -icoVector j
theorem icoAntipodal : IcoAntipodalStatement
```

```lean
def MeanPathUnitStatement : Prop :=
  ∀ t : ℝ, ∀ j, normSq (meanPath t j) = 1
theorem meanPathUnit : MeanPathUnitStatement
```

```lean
def MomentConstantStatement : Prop := moment (fun _ => 1) = 1
theorem momentConstant : MomentConstantStatement
```

```lean
def ProductFactorizationStatement : Prop :=
  ∀ n : ℕ, ∀ (α : Fin n → Type) [∀ x, Fintype (α x)],
    ∀ w : (x : Fin n) → α x → ℝ, ∀ v : (x : Fin n) → α x → Vec3,
    ∀ f : Fin n → Vec3 → ℝ,
      productSum α w v (fun a => ∏ x, f x (a x)) =
        ∏ x, finiteFunctional (w x) (v x) (f x)
theorem productFactorization : ProductFactorizationStatement
```

```lean
def SiteLawDecompositionStatement : Prop :=
  (∀ f : Vec3 → ℝ, siteFunctional .U f = moment f) ∧
  ∀ f : Vec3 → ℝ, siteFunctional .D f = (3 / 5) * moment f + (2 / 5) * f 0
theorem siteLawDecomposition : SiteLawDecompositionStatement
```

```lean
def SiteWeightStatement : Prop :=
  ∀ s : Status, s = .U ∨ s = .D →
    (∀ j : SpinLetter, 0 ≤ spinWeight s j) ∧
    ∀ j : IcoLetter, 0 < spinWeight s (some j)
theorem siteWeight : SiteWeightStatement
```

```lean
def TensorZeroMixtureStatement : Prop :=
  ∀ L : (Vec3 → ℝ) → ℝ, ∀ c q : ℝ, TensorLaw L c →
    TensorLaw (fun f => q * L f + (1 - q) * f 0) (q * c)
theorem tensorZeroMixture : TensorZeroMixtureStatement
```

## Exported theorem signatures

[productFactorization](/home/ubuntu/aklt/wt/BP_MOM/AKLT/Blueprint/Mom/NodesCore.lean:76)

```lean
theorem productFactorization : ProductFactorizationStatement
```

[tensorZeroMixture](/home/ubuntu/aklt/wt/BP_MOM/AKLT/Blueprint/Mom/NodesCore.lean:98)

```lean
theorem tensorZeroMixture : TensorZeroMixtureStatement
```

[rationalStatusMoment_nonneg](/home/ubuntu/aklt/wt/BP_MOM/AKLT/Blueprint/Mom/NodesCore.lean:115)

```lean
theorem rationalStatusMoment_nonneg (s : Status) (m : Fin 3 → ℕ) :
    0 ≤ (rationalStatusMoment s m : ℝ)
```

[frameOptionSum](/home/ubuntu/aklt/wt/BP_MOM/AKLT/Blueprint/Mom/NodesExact.lean:35)

```lean
theorem frameOptionSum : FrameOptionSumStatement
```

[freeEvaluation](/home/ubuntu/aklt/wt/BP_MOM/AKLT/Blueprint/Mom/NodesFinite.lean:68)

```lean
theorem freeEvaluation : FreeEvaluationStatement
```

[normSq_nonneg](/home/ubuntu/aklt/wt/BP_MOM/AKLT/Blueprint/Mom/NodesFinite.lean:108)

```lean
theorem normSq_nonneg (a : Vec3) : 0 ≤ normSq a
```

[emptyPartition](/home/ubuntu/aklt/wt/BP_MOM/AKLT/Blueprint/Mom/NodesFinite.lean:117)

```lean
theorem emptyPartition : EmptyPartitionStatement
```

[meanPathUnit](/home/ubuntu/aklt/wt/BP_MOM/AKLT/Blueprint/Mom/NodesMean.lean:100)

```lean
theorem meanPathUnit : MeanPathUnitStatement
```

[icoAntipodal](/home/ubuntu/aklt/wt/BP_MOM/AKLT/Blueprint/Mom/NodesMoments.lean:20)

```lean
theorem icoAntipodal : IcoAntipodalStatement
```

[momentConstant](/home/ubuntu/aklt/wt/BP_MOM/AKLT/Blueprint/Mom/NodesMoments.lean:49)

```lean
theorem momentConstant : MomentConstantStatement
```

[siteLawDecomposition](/home/ubuntu/aklt/wt/BP_MOM/AKLT/Blueprint/Mom/NodesMoments.lean:58)

```lean
theorem siteLawDecomposition : SiteLawDecompositionStatement
```

[siteWeight](/home/ubuntu/aklt/wt/BP_MOM/AKLT/Blueprint/Mom/NodesMoments.lean:75)

```lean
theorem siteWeight : SiteWeightStatement
```

[productFunctional_eq_productSum](/home/ubuntu/aklt/wt/BP_MOM/AKLT/Blueprint/Mom/Assembly.lean:15)

```lean
theorem productFunctional_eq_productSum {n : ℕ} (s : Fin n → Status)
    (f : (Fin n → Vec3) → ℝ) :
    productFunctional s f = productSum (fun _ : Fin n => SpinLetter)
      (fun x => spinWeight (s x)) (fun _ => spinVector) f
```

[quadrature_congruence](/home/ubuntu/aklt/wt/BP_MOM/AKLT/Blueprint/Mom/Assembly.lean:25)

```lean
theorem quadrature_congruence
    (hExpand : PolynomialExpansionStatement) (hFactor : ProductFactorizationStatement)
    {n : ℕ} (α β : Fin n → Type) [∀ x, Fintype (α x)] [∀ x, Fintype (β x)]
    (w : (x : Fin n) → α x → ℝ) (v : (x : Fin n) → α x → Vec3)
    (w' : (x : Fin n) → β x → ℝ) (v' : (x : Fin n) → β x → Vec3)
    (h : ∀ x, ∀ m : Fin 3 → ℕ, (∑ i, m i) ≤ 4 →
      finiteFunctional (w x) (v x) (mono m) = finiteFunctional (w' x) (v' x) (mono m))
    (p : MvPolynomial (Fin n × Fin 3) ℝ) (hp : SeparateDegreeFour p) :
    productSum α w v (fun a => MvPolynomial.eval (fun z => a z.1 z.2) p) =
      productSum β w' v' (fun a => MvPolynomial.eval (fun z => a z.1 z.2) p)
```

[scaledMoment_status](/home/ubuntu/aklt/wt/BP_MOM/AKLT/Blueprint/Mom/Assembly.lean:46)

```lean
theorem scaledMoment_status (s : Status) (hs : s = .U ∨ s = .D) (m : Fin 3 → ℕ) :
    scaledMoment (if s = .D then (3 / 5 : ℝ) else 1) m =
      (rationalStatusMoment s m : ℝ)
```

[moments_of_leaves](/home/ubuntu/aklt/wt/BP_MOM/AKLT/Blueprint/Mom/Assembly.lean:57)

```lean
theorem moments_of_leaves
    (hInject : IcoInjectivityStatement) (hUnit : IcoUnitStatement)
    (hAnti : IcoAntipodalStatement) (hOdd : OddMonomialStatement)
    (hSecond : SecondScalarMomentStatement) (hFourth : FourthScalarMomentStatement)
    (hMixed : MixedScalarMomentStatement) (hReconstruct : ScalarTensorReconstructionStatement)
    (hMonomial : TensorMonomialStatement) (hOrthogonal : OrthogonalTensorStatement)
    (hExpand : PolynomialExpansionStatement) (hFactor : ProductFactorizationStatement) :
    AKLT.Blueprint.Top.MomentsStatement
```

[spinVector_normSq_le_one](/home/ubuntu/aklt/wt/BP_MOM/AKLT/Blueprint/Mom/Assembly.lean:103)

```lean
theorem spinVector_normSq_le_one (hUnit : IcoUnitStatement) (j : SpinLetter) :
    normSq (spinVector j) ≤ 1
```

[network_weight_nonneg](/home/ubuntu/aklt/wt/BP_MOM/AKLT/Blueprint/Mom/Assembly.lean:110)

```lean
theorem network_weight_nonneg (hUnit : IcoUnitStatement) (hBall : BallDotBoundsStatement)
    {n : ℕ} (D : FiniteSpinNetwork n) (hD : D.Valid) (pinned : Bool)
    (σ : Fin n → SpinLetter) : 0 ≤ D.weight pinned σ
```

[network_partition_positive](/home/ubuntu/aklt/wt/BP_MOM/AKLT/Blueprint/Mom/Assembly.lean:130)

```lean
theorem network_partition_positive
    (hUnit : IcoUnitStatement) (hAvoid : LetterAvoidanceStatement)
    (hGreedy : GreedyAssignmentStatement) (hBall : BallDotBoundsStatement)
    {n : ℕ} (D : FiniteSpinNetwork n) (hD : D.Valid) (pinned : Bool) :
    0 < D.partition pinned (fun _ => 1)
```

[finiteFacts_of_leaves](/home/ubuntu/aklt/wt/BP_MOM/AKLT/Blueprint/Mom/Assembly.lean:157)

```lean
theorem finiteFacts_of_leaves
    (hMoments : AKLT.Blueprint.Top.MomentsStatement)
    (hBall : BallDotBoundsStatement) (hAvoid : LetterAvoidanceStatement)
    (hGreedy : GreedyAssignmentStatement) (hCoeff : FreeCoefficientsStatement)
    (hDegree : FreeDegreeStatement) (hEval : FreeEvaluationStatement)
    (hFibre : TwoSiteFactorizationStatement) (hCondition : FactorizedConditioningStatement)
    (hExpand : PolynomialExpansionStatement) (hFactor : ProductFactorizationStatement) :
    AKLT.Blueprint.Top.FiniteFactsStatement
```

[normSq_div](/home/ubuntu/aklt/wt/BP_MOM/AKLT/Blueprint/Mom/Assembly.lean:197)

```lean
theorem normSq_div (v : Vec3) (c : ℝ) :
    normSq (fun i => v i / c) = normSq v / c^2
```

[siteFunctional_sum](/home/ubuntu/aklt/wt/BP_MOM/AKLT/Blueprint/Mom/Assembly.lean:202)

```lean
theorem siteFunctional_sum (s : Status) {m : ℕ} (t : Fin m → ℝ)
    (f : Fin m → Vec3 → ℝ) :
    siteFunctional s (fun v => ∑ η, t η * f η v) =
      ∑ η, t η * siteFunctional s (f η)
```

[siteFunctional_mixture](/home/ubuntu/aklt/wt/BP_MOM/AKLT/Blueprint/Mom/Assembly.lean:216)

```lean
theorem siteFunctional_mixture (s : Status) {m : ℕ} (t : Fin m → ℝ)
    (W : Vec3 → ℝ) (f : Fin m → Vec3 → ℝ)
    (hW : ∀ v, W v = ∑ η, t η * f η v) :
    siteFunctional s W = ∑ η, t η * siteFunctional s (f η) ∧
      ∀ i, siteFunctional s (fun v => v i * W v) =
        ∑ η, t η * siteFunctional s (fun v => v i * f η v)
```

[unitTriple_bound](/home/ubuntu/aklt/wt/BP_MOM/AKLT/Blueprint/Mom/Assembly.lean:236)

```lean
theorem unitTriple_bound
    (hA : TripleNormalizerStatement) (hV : TripleNumeratorStatement)
    (hGeometry : TripleGeometryStatement) (hSOS : TripleSOSIdentityStatement)
    (a : Fin 3 → Vec3) (ha : ∀ j, normSq (a j) = 1) :
    1 / 2 ≤ siteFunctional .U (localProduct a) ∧
      normSq (localMean .U a) ≤ (3 / 5 : ℝ)^2
```

[threeFactorMean_of_leaves](/home/ubuntu/aklt/wt/BP_MOM/AKLT/Blueprint/Mom/Assembly.lean:261)

```lean
theorem threeFactorMean_of_leaves
    (hA : TripleNormalizerStatement) (hV : TripleNumeratorStatement)
    (hGeometry : TripleGeometryStatement) (hSOS : TripleSOSIdentityStatement)
    (hSplit : BallFieldSplitStatement) (hMix : ProductMixtureStatement)
    (hEstimate : PositiveMixtureEstimateStatement) (hD : DepletedContractionStatement)
    (hPathUnit : MeanPathUnitStatement) (hContinuous : MeanPathContinuityStatement)
    (hEndpoints : MeanPathEndpointsStatement) (hCovariance : MeanCovarianceStatement)
    (hNorm : OrthogonalNormStatement) (hTransport : OrthogonalTransportStatement) :
    AKLT.Blueprint.Top.ThreeFactorMeanStatement
```

[exact_of_leaves](/home/ubuntu/aklt/wt/BP_MOM/AKLT/Blueprint/Mom/Assembly.lean:317)

```lean
theorem exact_of_leaves
    (hSingle : SingleSiteQuadratureStatement) (hExpand : PolynomialExpansionStatement)
    (hFactor : ProductFactorizationStatement) : AKLT.Blueprint.Top.ExactStatement
```

[all_of_leaves](/home/ubuntu/aklt/wt/BP_MOM/AKLT/Blueprint/Mom/Assembly.lean:340)

```lean
theorem all_of_leaves : MomentInputs → FiniteInputs → MeanInputs →
    SingleSiteQuadratureStatement → AllTargets
```

[icoSet_card](/home/ubuntu/aklt/wt/BP_MOM/AKLT/Blueprint/Mom/Assembly.lean:355)

```lean
theorem icoSet_card (h : IcoInjectivityStatement) : icoSet.card = 12
```

[freeMean_nonneg](/home/ubuntu/aklt/wt/BP_MOM/AKLT/Blueprint/Mom/Assembly.lean:362)

```lean
theorem freeMean_nonneg (h : AKLT.Blueprint.Top.FiniteFactsStatement)
    {n : ℕ} (D : FiniteSpinNetwork n) (hD : D.Valid) (pairs : List (Fin n × Fin n))
    (hIncidence : ∀ x, (D.bonds.filter fun e => e.1 = x ∨ e.2 = x).card +
      (pairs.filter fun e => e.1 = x).length + (pairs.filter fun e => e.2 = x).length ≤ 4) :
    0 ≤ D.partition false (fun a => (pairs.map fun e => dot (a e.1) (a e.2)).prod) /
      D.partition false (fun _ => 1)
```

[normalize_probability](/home/ubuntu/aklt/wt/BP_MOM/AKLT/Blueprint/Mom/Assembly.lean:371)

```lean
theorem normalize_probability {Ω : Type} [Fintype Ω] (w : Ω → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hZ : 0 < ∑ a, w a) : Probability (normalize w)
```

[conditionOn_probability](/home/ubuntu/aklt/wt/BP_MOM/AKLT/Blueprint/Mom/Assembly.lean:379)

```lean
theorem conditionOn_probability {Ω : Type} [Fintype Ω] (p : Ω → ℝ)
    (hp : Probability p) (E : Ω → Prop) (hE : 0 < eventMass p E) :
    Probability (conditionOn p E)
```

[network_probability_of_parts](/home/ubuntu/aklt/wt/BP_MOM/AKLT/Blueprint/Mom/Assembly.lean:392)

```lean
theorem network_probability_of_parts
    (hMoments : AKLT.Blueprint.Top.MomentsStatement)
    (hFacts : AKLT.Blueprint.Top.FiniteFactsStatement) (hBall : BallDotBoundsStatement)
    {n : ℕ} (D : FiniteSpinNetwork n) (hD : D.Valid) (pinned : Bool) :
    Probability (normalize (D.weight pinned))
```

[probability_mean_normSq_le_one](/home/ubuntu/aklt/wt/BP_MOM/AKLT/Blueprint/Mom/Assembly.lean:407)

```lean
theorem probability_mean_normSq_le_one (hEstimate : PositiveMixtureEstimateStatement)
    {Ω : Type} [Fintype Ω] (p : Ω → ℝ) (hp : Probability p) (v : Ω → Vec3)
    (hv : ∀ a, normSq (v a) ≤ 1) :
    normSq (fun i => ∑ a, p a * v a i) ≤ 1
```

[conditioned_spin_mean_normSq_le_one](/home/ubuntu/aklt/wt/BP_MOM/AKLT/Blueprint/Mom/Assembly.lean:417)

```lean
theorem conditioned_spin_mean_normSq_le_one
    (hMoments : AKLT.Blueprint.Top.MomentsStatement)
    (hEstimate : PositiveMixtureEstimateStatement) {n : ℕ}
    (p : Weight (Fin n → SpinLetter)) (hp : Probability p)
    (E : (Fin n → SpinLetter) → Prop) (hE : 0 < eventMass p E) (x : Fin n) :
    normSq (fun i => ∑ τ, conditionOn p E τ * spinVector (τ x) i) ≤ 1
```

[conditional_threeFactorMean_of_leaves](/home/ubuntu/aklt/wt/BP_MOM/AKLT/Blueprint/Mom/Assembly.lean:429)

```lean
theorem conditional_threeFactorMean_of_leaves
    (hMean : AKLT.Blueprint.Top.ThreeFactorMeanStatement)
    (hReduction : OneSiteConditionalReductionStatement)
    {n : ℕ} (D : FiniteSpinNetwork n) (hD : D.Valid) (pinned : Bool)
    (x : Fin n) (hPin : D.pinCount x = 0)
    (hDegree : (D.bonds.filter fun e => e.1 = x ∨ e.2 = x).card ≤ 3)
    (σ : Fin n → SpinLetter)
    (hMass : 0 < eventMass (normalize (D.weight pinned)) (oneSiteFibre x σ)) :
    normSq (conditionalSpinMean (normalize (D.weight pinned)) x σ) ≤ (3 / 5 : ℝ)^2
```

[interaction_exact_of_leaves](/home/ubuntu/aklt/wt/BP_MOM/AKLT/Blueprint/Mom/Assembly.lean:445)

```lean
theorem interaction_exact_of_leaves
    (hSingle : SingleSiteQuadratureStatement) (hExpand : PolynomialExpansionStatement)
    (hDegree : InteractionDegreeStatement)
    {n : ℕ} (k : Fin n → ℕ) (F : (x : Fin n) → FrameData (k x))
    (hF : ∀ x, MomentLaw (F x)) (s : Fin n → Status) (hs : ∀ x, s x = .U ∨ s x = .D)
    (bonds : List ((Fin n × Fin n) × ℝ)) (pins : List ((Fin n × Vec3) × ℝ))
    (p : MvPolynomial (Fin n × Fin 3) ℝ)
    (hp : ∀ m ∈ p.support, ∀ x : Fin n,
      (∑ i : Fin 3, m (x, i)) + interactionOccurrences bonds pins x ≤ 4) :
    productSum (fun x => Option (Fin (k x)))
      (fun x => frameWeight (F x) (s x)) (fun x => frameAtom (F x))
      (fun a => MvPolynomial.eval (fun z => a z.1 z.2) (interactionPolynomial bonds pins p)) =
    productSum (fun _ : Fin n => SpinLetter) (fun x => spinWeight (s x))
      (fun _ => spinVector)
      (fun a => MvPolynomial.eval (fun z => a z.1 z.2) (interactionPolynomial bonds pins p))
```
