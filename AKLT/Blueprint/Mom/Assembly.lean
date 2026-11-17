module
public import AKLT.Blueprint.Mom.NodesConsequences

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-! Kernel-checked assembly implications for the four Section 2 interfaces.
All open mathematical inputs to the four target theorems are closed Props.
The generic algebra below only rearranges finite sums and supplied identities. -/

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.Blueprint.Mom

/-- Changing the finite enumeration does not change the product sum. The two
definitions synthesize different decidable equality instances on `Fin n`. -/
theorem productFunctional_eq_productSum {n : ℕ} (s : Fin n → Status)
    (f : (Fin n → Vec3) → ℝ) :
    productFunctional s f = productSum (fun _ : Fin n => SpinLetter)
      (fun x => spinWeight (s x)) (fun _ => spinVector) f := by
  unfold productFunctional productSum
  congr 1
  ext
  simp

/-- Finite tensorization of equality of the admissible single-site monomials. -/
theorem quadrature_congruence
    (hExpand : PolynomialExpansionStatement) (hFactor : ProductFactorizationStatement)
    {n : ℕ} (α β : Fin n → Type) [∀ x, Fintype (α x)] [∀ x, Fintype (β x)]
    (w : (x : Fin n) → α x → ℝ) (v : (x : Fin n) → α x → Vec3)
    (w' : (x : Fin n) → β x → ℝ) (v' : (x : Fin n) → β x → Vec3)
    (h : ∀ x, ∀ m : Fin 3 → ℕ, (∑ i, m i) ≤ 4 →
      finiteFunctional (w x) (v x) (mono m) = finiteFunctional (w' x) (v' x) (mono m))
    (p : MvPolynomial (Fin n × Fin 3) ℝ) (hp : SeparateDegreeFour p) :
    productSum α w v (fun a => MvPolynomial.eval (fun z => a z.1 z.2) p) =
      productSum β w' v' (fun a => MvPolynomial.eval (fun z => a z.1 z.2) p) := by
  classical
  rw [hExpand n α w v p, hExpand n β w' v' p]
  apply Finset.sum_congr rfl
  intro m hm
  rw [hFactor n α w v, hFactor n β w' v']
  congr 1
  apply Finset.prod_congr rfl
  intro x _
  exact h x (fun i => m (x, i)) (hp m hm x)

/-- Convert the generic tensor scale to the shared exact rational convention. -/
theorem scaledMoment_status (s : Status) (hs : s = .U ∨ s = .D) (m : Fin 3 → ℕ) :
    scaledMoment (if s = .D then (3 / 5 : ℝ) else 1) m =
      (rationalStatusMoment s m : ℝ) := by
  rcases hs with rfl | rfl
  all_goals
    by_cases h : (∑ i, m i) = 0
    · simp [scaledMoment, rationalStatusMoment, rationalMoment, h]
    · simp [scaledMoment, rationalStatusMoment, h]

/-- `l:moments`: reconstruct tensors, transfer the zero-atom mixture, contract
orthogonal substitutions, and tensorize the single-site identities. -/
theorem moments_of_leaves
    (hInject : IcoInjectivityStatement) (hUnit : IcoUnitStatement)
    (hAnti : IcoAntipodalStatement) (hOdd : OddMonomialStatement)
    (hSecond : SecondScalarMomentStatement) (hFourth : FourthScalarMomentStatement)
    (hMixed : MixedScalarMomentStatement) (hReconstruct : ScalarTensorReconstructionStatement)
    (hMonomial : TensorMonomialStatement) (hOrthogonal : OrthogonalTensorStatement)
    (hExpand : PolynomialExpansionStatement) (hFactor : ProductFactorizationStatement) :
    AKLT.Blueprint.Top.MomentsStatement := by
  have hT : TensorLaw moment 1 :=
    hReconstruct moment momentConstant hOdd hSecond hFourth hMixed
  have hU : siteFunctional .U = moment := funext siteLawDecomposition.1
  have hD : siteFunctional .D =
      fun f => (3 / 5) * moment f + (2 / 5) * f 0 :=
    funext siteLawDecomposition.2
  have hTD : TensorLaw (siteFunctional .D) (3 / 5) := by
    rw [hD]
    convert tensorZeroMixture moment 1 (3 / 5) hT using 1 <;> norm_num
  have hSite : ∀ s : Status, s = .U ∨ s = .D →
      TensorLaw (siteFunctional s) (if s = .D then (3 / 5 : ℝ) else 1) := by
    intro s hs
    rcases hs with rfl | rfl
    · simpa [hU] using hT
    · simpa only [reduceIte] using hTD
  refine ⟨hInject, hUnit, hAnti, hT.1, hT.2.1, hT.2.2.1, hT.2.2.2.1, ?_, ?_, ?_⟩
  · intro i j k l
    simpa only [one_mul] using hT.2.2.2.2 i j k l
  · intro m hm s hs
    change siteFunctional s (mono m) = _
    exact (hMonomial (siteFunctional s) _ (hSite s hs) m hm).trans
      (scaledMoment_status s hs m)
  · intro n s hs p hp R hR
    rw [productFunctional_eq_productSum, productFunctional_eq_productSum]
    change productSum (fun _ : Fin n => SpinLetter) (fun x => spinWeight (s x))
      (fun x j => (R x).mulVec (spinVector j))
        (fun a => MvPolynomial.eval (fun z => a z.1 z.2) p) =
      productSum (fun _ : Fin n => SpinLetter) (fun x => spinWeight (s x))
        (fun _ => spinVector) (fun a => MvPolynomial.eval (fun z => a z.1 z.2) p)
    apply quadrature_congruence hExpand hFactor
    · intro x m hm
      have ht := hOrthogonal SpinLetter (spinWeight (s x)) spinVector _ (hSite (s x) (hs x))
        (R x) (hR x)
      exact (hMonomial _ _ ht m hm).trans
        (hMonomial _ _ (hSite (s x) (hs x)) m hm).symm
    · exact hp

/-- The common SpinLetter support is in the ball even at zero-weight atoms. -/
theorem spinVector_normSq_le_one (hUnit : IcoUnitStatement) (j : SpinLetter) :
    normSq (spinVector j) ≤ 1 := by
  cases j with
  | none => norm_num [spinVector, normSq, dot]
  | some j => exact le_of_eq (hUnit j)

/-- Nonnegative weights follow pointwise from the site masses and ball factors. -/
theorem network_weight_nonneg (hUnit : IcoUnitStatement) (hBall : BallDotBoundsStatement)
    {n : ℕ} (D : FiniteSpinNetwork n) (hD : D.Valid) (pinned : Bool)
    (σ : Fin n → SpinLetter) : 0 ≤ D.weight pinned σ := by
  classical
  apply mul_nonneg
  · apply mul_nonneg
    · exact Finset.prod_nonneg (fun x _ => (siteWeight (D.status x) (hD.1 x)).1 (σ x))
    · apply Finset.prod_nonneg
      intro e _
      exact (hBall _ _ (spinVector_normSq_le_one hUnit _) (spinVector_normSq_le_one hUnit _)).1
  · apply Finset.prod_nonneg
    intro x _
    apply Finset.prod_nonneg
    intro j _
    cases pinned with
    | false => norm_num
    | true => exact (hBall _ _ (le_of_eq (D.pin x j).property)
        (spinVector_normSq_le_one hUnit _)).1

/-- A greedily chosen all-unit configuration is a strictly positive summand. -/
theorem network_partition_positive
    (hUnit : IcoUnitStatement) (hAvoid : LetterAvoidanceStatement)
    (hGreedy : GreedyAssignmentStatement) (hBall : BallDotBoundsStatement)
    {n : ℕ} (D : FiniteSpinNetwork n) (hD : D.Valid) (pinned : Bool) :
    0 < D.partition pinned (fun _ => 1) := by
  classical
  obtain ⟨σ, hb, hp⟩ := hGreedy IcoLetter icoVector (fun j => le_of_eq (hUnit j))
    hAvoid n D hD
  have hw : 0 < D.weight pinned (fun x => some (σ x)) := by
    apply mul_pos
    · apply mul_pos
      · exact Finset.prod_pos (fun x _ => (siteWeight (D.status x) (hD.1 x)).2 (σ x))
      · exact Finset.prod_pos (fun e he => hb e he)
    · apply Finset.prod_pos
      intro x _
      apply Finset.prod_pos
      intro j _
      cases pinned with
      | false => norm_num
      | true => exact hp x j
  change 0 < ∑ τ, D.weight pinned τ * 1
  simp only [mul_one]
  exact Finset.sum_pos' (fun τ _ => network_weight_nonneg hUnit hBall D hD pinned τ)
    ⟨(fun x => some (σ x)), Finset.mem_univ _, hw⟩

/-- `l:finitefacts`: positive summands, coefficientwise free positivity under
the complete degree test, and factorization on positive conditioning fibres. -/
theorem finiteFacts_of_leaves
    (hMoments : AKLT.Blueprint.Top.MomentsStatement)
    (hBall : BallDotBoundsStatement) (hAvoid : LetterAvoidanceStatement)
    (hGreedy : GreedyAssignmentStatement) (hCoeff : FreeCoefficientsStatement)
    (hDegree : FreeDegreeStatement) (hEval : FreeEvaluationStatement)
    (hFibre : TwoSiteFactorizationStatement) (hCondition : FactorizedConditioningStatement)
    (hExpand : PolynomialExpansionStatement) (hFactor : ProductFactorizationStatement) :
    AKLT.Blueprint.Top.FiniteFactsStatement := by
  classical
  rcases hMoments with ⟨_, hUnit, _, _, _, _, _, _, hMonomial, _⟩
  constructor
  · intro s hs j hj
    exact spinVector_normSq_le_one hUnit j
  · intro n D hD
    refine ⟨network_partition_positive hUnit hAvoid hGreedy hBall D hD true,
      network_partition_positive hUnit hAvoid hGreedy hBall D hD false, ?_, ?_⟩
    · intro pairs hIncidence
      rw [hEval n D pairs]
      rw [productFunctional_eq_productSum]
      change 0 ≤ productSum (fun _ : Fin n => SpinLetter) (fun x => spinWeight (D.status x))
        (fun _ => spinVector) (fun a => MvPolynomial.eval (fun z => a z.1 z.2)
          (freePolynomial D pairs))
      rw [hExpand]
      apply Finset.sum_nonneg
      intro m hm
      apply mul_nonneg (hCoeff n D pairs m)
      rw [hFactor]
      apply Finset.prod_nonneg
      intro x _
      change 0 ≤ siteFunctional (D.status x) (fun v => ∏ i, v i ^ m (x, i))
      rw [hMonomial _ (hDegree n D hD pairs hIncidence m hm x) _ (hD.1 x)]
      exact rationalStatusMoment_nonneg _ _
    · intro pinned x y hxy hnot hnot' σ
      dsimp only
      intro hMass a b
      obtain ⟨C, u, v, _, _, _, hf⟩ := hFibre n D hD pinned x y hxy hnot hnot' σ
      exact hCondition n (D.weight pinned) (network_weight_nonneg hUnit hBall D hD pinned)
        x y hxy σ C u v hf hMass a b

/-- Squared Euclidean norm commutes with scalar division, including division by zero. -/
theorem normSq_div (v : Vec3) (c : ℝ) :
    normSq (fun i => v i / c) = normSq v / c^2 := by
  simp only [normSq, dot, div_mul_div_comm, ← Finset.sum_div, pow_two]

/-- Finite linearity for the one-site law. -/
theorem siteFunctional_sum (s : Status) {m : ℕ} (t : Fin m → ℝ)
    (f : Fin m → Vec3 → ℝ) :
    siteFunctional s (fun v => ∑ η, t η * f η v) =
      ∑ η, t η * siteFunctional s (f η) := by
  unfold siteFunctional
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro η _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Evaluate both scalar and vector numerators of a pointwise finite mixture. -/
theorem siteFunctional_mixture (s : Status) {m : ℕ} (t : Fin m → ℝ)
    (W : Vec3 → ℝ) (f : Fin m → Vec3 → ℝ)
    (hW : ∀ v, W v = ∑ η, t η * f η v) :
    siteFunctional s W = ∑ η, t η * siteFunctional s (f η) ∧
      ∀ i, siteFunctional s (fun v => v i * W v) =
        ∑ η, t η * siteFunctional s (fun v => v i * f η v) := by
  constructor
  · rw [funext hW]
    exact siteFunctional_sum s t f
  · intro i
    have h : (fun v => v i * W v) = fun v => ∑ η, t η * (v i * f η v) := by
      funext v
      rw [hW, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro η _
      ring
    rw [h]
    exact siteFunctional_sum s t _

/-- The SOS identity yields the unit-triple estimate without square roots. -/
theorem unitTriple_bound
    (hA : TripleNormalizerStatement) (hV : TripleNumeratorStatement)
    (hGeometry : TripleGeometryStatement) (hSOS : TripleSOSIdentityStatement)
    (a : Fin 3 → Vec3) (ha : ∀ j, normSq (a j) = 1) :
    1 / 2 ≤ siteFunctional .U (localProduct a) ∧
      normSq (localMean .U a) ≤ (3 / 5 : ℝ)^2 := by
  obtain ⟨hLower, hX, hY, hZ⟩ := hGeometry a ha
  have hPos : 0 < siteFunctional .U (localProduct a) := by rw [hA]; linarith
  have hSOSnonneg : 0 ≤ tripleSOS a := by dsimp [tripleSOS]; positivity
  have hMean : localMean .U a =
      fun i => tripleV a i / (15 * siteFunctional .U (localProduct a)) := by
    funext i
    change siteFunctional .U (fun v => v i * localProduct a v) /
      siteFunctional .U (localProduct a) = _
    have hv : siteFunctional .U (fun v => v i * localProduct a v) = tripleV a i / 15 := by
      linarith [hV a i]
    rw [hv, div_div]
  refine ⟨by rw [hA a]; exact hLower, ?_⟩
  rw [hMean, normSq_div]
  apply (div_le_iff₀ (sq_pos_of_pos (mul_pos (by norm_num) hPos))).2
  rw [hA]
  nlinarith [hSOS a ha]

/-- `l:35`: combine the unit SOS estimate, eight-term mixtures, the D
contraction, and the continuous path followed by orthogonal transport. -/
theorem threeFactorMean_of_leaves
    (hA : TripleNormalizerStatement) (hV : TripleNumeratorStatement)
    (hGeometry : TripleGeometryStatement) (hSOS : TripleSOSIdentityStatement)
    (hSplit : BallFieldSplitStatement) (hMix : ProductMixtureStatement)
    (hEstimate : PositiveMixtureEstimateStatement) (hD : DepletedContractionStatement)
    (hPathUnit : MeanPathUnitStatement) (hContinuous : MeanPathContinuityStatement)
    (hEndpoints : MeanPathEndpointsStatement) (hCovariance : MeanCovarianceStatement)
    (hNorm : OrthogonalNormStatement) (hTransport : OrthogonalTransportStatement) :
    AKLT.Blueprint.Top.ThreeFactorMeanStatement := by
  have hBound : ∀ k : ℕ, k ≤ 3 → ∀ a : Fin k → Vec3,
      (∀ j, normSq (a j) ≤ 1) → ∀ s : Status, s = .U ∨ s = .D →
      0 < siteFunctional s (localProduct a) ∧ normSq (localMean s a) ≤ (3 / 5 : ℝ)^2 := by
    intro k hk a ha s hs
    obtain ⟨t, b, ht, htSum, hProduct⟩ := hMix k hk a (fun j => hSplit (a j) (ha j))
    let A : Fin 8 → ℝ := fun η => siteFunctional .U (localProduct (fun j => (b η j).val))
    let B : Fin 8 → Vec3 := fun η i =>
      siteFunctional .U (fun v => v i * localProduct (fun j => (b η j).val) v)
    have hEach := fun η => unitTriple_bound hA hV hGeometry hSOS
      (fun j => (b η j).val) (fun j => (b η j).property)
    have hEst := hEstimate (Fin 8) t A B (3 / 5) (by norm_num) ht htSum
      (fun η => (hEach η).1) (fun η => (hEach η).2)
    obtain ⟨hScalar, hVector⟩ := siteFunctional_mixture .U t (localProduct a)
      (fun η => localProduct (fun j => (b η j).val)) hProduct
    have hPosU : 0 < siteFunctional .U (localProduct a) := by
      rw [hScalar]
      exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hEst.1
    have hNormU : normSq (localMean .U a) ≤ (3 / 5 : ℝ)^2 := by
      unfold localMean
      simp_rw [hScalar, hVector]
      exact hEst.2
    rcases hs with rfl | rfl
    · exact ⟨hPosU, hNormU⟩
    · exact ⟨(hD k a hPosU).1, (hD k a hPosU).2.trans hNormU⟩
  refine ⟨hBound, ?_⟩
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    exact (hBound 3 (by omega) (fun j => (a j).val)
      (fun j => le_of_eq (a j).property) .U (Or.inl rfl)).2
  · intro hb
    have hInterval : (0 : ℝ) ≤ meanPathEnd := by unfold meanPathEnd; positivity
    have hMember : normSq b ∈ Set.Icc
        (normSq (localMean .U (meanPath meanPathEnd)))
        (normSq (localMean .U (meanPath 0))) := by
      rw [hEndpoints.1, hEndpoints.2]
      exact ⟨normSq_nonneg b, hb⟩
    obtain ⟨t, _, ht⟩ := intermediate_value_Icc' hInterval hContinuous hMember
    obtain ⟨R, hR, hMap⟩ := hTransport (localMean .U (meanPath t)) b ht
    let a : Fin 3 → UnitVector := fun j =>
      ⟨R.mulVec (meanPath t j), by rw [hNorm R hR, hPathUnit]⟩
    refine ⟨a, ?_⟩
    change localMean .U (fun j => R.mulVec (meanPath t j)) = b
    rw [hCovariance (meanPath t) (hPathUnit t) R hR, hMap]

/-- `l:exact`: compare each admissible monomial at each site and apply the
same finite tensorization used by the covariance proof. -/
theorem exact_of_leaves
    (hSingle : SingleSiteQuadratureStatement) (hExpand : PolynomialExpansionStatement)
    (hFactor : ProductFactorizationStatement) : AKLT.Blueprint.Top.ExactStatement := by
  classical
  intro n k F hF s hs p hp
  have hQ := quadrature_congruence hExpand hFactor
    (fun x => Option (Fin (k x))) (fun _ : Fin n => SpinLetter)
    (fun x => frameWeight (F x) (s x)) (fun x => frameAtom (F x))
    (fun x => spinWeight (s x)) (fun _ => spinVector)
    (fun x m hm => (frameOptionSum (k x) (F x) (s x) (hs x) (mono m)).trans
      (hSingle (k x) (F x) (hF x) (s x) (hs x) m hm)) p hp
  dsimp only [productSum, frameWeight, frameAtom, productFunctional] at hQ ⊢
  convert hQ using 1 <;> congr 1 <;> ext <;> simp
  rename_i a
  congr 2
  · funext x
    cases a x <;> simp
  · congr 1
    funext z
    cases a z.1 <;> simp

/-- All assigned targets from open leaves only: the previously assembled
moments theorem is supplied internally to finite facts. No external Top premise remains. -/
theorem all_of_leaves : MomentInputs → FiniteInputs → MeanInputs →
    SingleSiteQuadratureStatement → AllTargets := by
  rintro ⟨hi, hu, ho, hs, hf, hm, hr, ht, horth, he⟩
    ⟨hb, ha, hg, hc, hd, hfi, hco⟩
    ⟨hA, hV, hGeometry, hSOS, hSplit, hMix, hEstimate, hD, hPC, hPE, hCov, hNorm, hTrans⟩
    hSingle
  have hMoments := moments_of_leaves hi hu icoAntipodal ho hs hf hm hr ht horth he
    productFactorization
  exact ⟨hMoments,
    finiteFacts_of_leaves hMoments hb ha hg hc hd freeEvaluation hfi hco he productFactorization,
    threeFactorMean_of_leaves hA hV hGeometry hSOS hSplit hMix hEstimate hD meanPathUnit hPC hPE
      hCov hNorm hTrans,
    exact_of_leaves hSingle he productFactorization⟩

/-- `l:moments`, line 36: injectivity really gives twelve points in the set `D`. -/
theorem icoSet_card (h : IcoInjectivityStatement) : icoSet.card = 12 := by
  unfold icoSet
  rw [Finset.card_image_of_injective _ h]
  norm_num [IcoLetter, Fintype.card_prod]

/-- `l:finitefacts`, line 136: division by the strictly positive free
partition sum preserves the unnormalized nonnegative observable value. -/
theorem freeMean_nonneg (h : AKLT.Blueprint.Top.FiniteFactsStatement)
    {n : ℕ} (D : FiniteSpinNetwork n) (hD : D.Valid) (pairs : List (Fin n × Fin n))
    (hIncidence : ∀ x, (D.bonds.filter fun e => e.1 = x ∨ e.2 = x).card +
      (pairs.filter fun e => e.1 = x).length + (pairs.filter fun e => e.2 = x).length ≤ 4) :
    0 ≤ D.partition false (fun a => (pairs.map fun e => dot (a e.1) (a e.2)).prod) /
      D.partition false (fun _ => 1) := by
  exact div_nonneg ((h.2 n D hD).2.2.1 pairs hIncidence) (le_of_lt (h.2 n D hD).2.1)

/-- Normalize only after proving positive total mass. -/
theorem normalize_probability {Ω : Type} [Fintype Ω] (w : Ω → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hZ : 0 < ∑ a, w a) : Probability (normalize w) := by
  constructor
  · intro a
    exact div_nonneg (hw a) (le_of_lt hZ)
  · simp only [AKLT.Defs.normalize, ← Finset.sum_div, div_self (ne_of_gt hZ)]

/-- Positive-probability conditioning produces a genuine finite probability. -/
theorem conditionOn_probability {Ω : Type} [Fintype Ω] (p : Ω → ℝ)
    (hp : Probability p) (E : Ω → Prop) (hE : 0 < eventMass p E) :
    Probability (conditionOn p E) := by
  classical
  apply normalize_probability
  · intro a
    split_ifs
    · exact hp.1 a
    · exact le_rfl
  · exact hE

/-- `l:finitefacts`, lines 131–137: the actual network normalization is a
probability, including zero site masses and the zero-site network. -/
theorem network_probability_of_parts
    (hMoments : AKLT.Blueprint.Top.MomentsStatement)
    (hFacts : AKLT.Blueprint.Top.FiniteFactsStatement) (hBall : BallDotBoundsStatement)
    {n : ℕ} (D : FiniteSpinNetwork n) (hD : D.Valid) (pinned : Bool) :
    Probability (normalize (D.weight pinned)) := by
  have hZ : 0 < D.partition pinned (fun _ => 1) := by
    cases pinned with
    | false => exact (hFacts.2 n D hD).2.1
    | true => exact (hFacts.2 n D hD).1
  exact normalize_probability (D.weight pinned)
    (network_weight_nonneg hMoments.2.1 hBall D hD pinned)
    (by simpa only [FiniteSpinNetwork.partition, mul_one] using hZ)

/-- `l:finitefacts`, lines 193–194: any finite probability average of ball
vectors stays in the ball. This also applies to a conditional probability. -/
theorem probability_mean_normSq_le_one (hEstimate : PositiveMixtureEstimateStatement)
    {Ω : Type} [Fintype Ω] (p : Ω → ℝ) (hp : Probability p) (v : Ω → Vec3)
    (hv : ∀ a, normSq (v a) ≤ 1) :
    normSq (fun i => ∑ a, p a * v a i) ≤ 1 := by
  have h := hEstimate Ω p (fun _ => 1) v 1 (by norm_num) hp.1 hp.2
    (fun _ => by norm_num) (fun a => by simpa using hv a)
  simpa only [mul_one, hp.2, div_one, one_pow] using h.2

/-- `l:finitefacts`, lines 193–194: an actual conditional spin mean has
norm at most one, for every event of positive mass and every site. -/
theorem conditioned_spin_mean_normSq_le_one
    (hMoments : AKLT.Blueprint.Top.MomentsStatement)
    (hEstimate : PositiveMixtureEstimateStatement) {n : ℕ}
    (p : Weight (Fin n → SpinLetter)) (hp : Probability p)
    (E : (Fin n → SpinLetter) → Prop) (hE : 0 < eventMass p E) (x : Fin n) :
    normSq (fun i => ∑ τ, conditionOn p E τ * spinVector (τ x) i) ≤ 1 := by
  exact probability_mean_normSq_le_one hEstimate (conditionOn p E)
    (conditionOn_probability p hp E hE) (fun τ => spinVector (τ x))
    (fun τ => spinVector_normSq_le_one hMoments.2.1 (τ x))

/-- `l:35`, lines 290–294: the compact Top bound implies the paper's
conditional-mean consequence after identifying the one-site conditional law. -/
theorem conditional_threeFactorMean_of_leaves
    (hMean : AKLT.Blueprint.Top.ThreeFactorMeanStatement)
    (hReduction : OneSiteConditionalReductionStatement)
    {n : ℕ} (D : FiniteSpinNetwork n) (hD : D.Valid) (pinned : Bool)
    (x : Fin n) (hPin : D.pinCount x = 0)
    (hDegree : (D.bonds.filter fun e => e.1 = x ∨ e.2 = x).card ≤ 3)
    (σ : Fin n → SpinLetter)
    (hMass : 0 < eventMass (normalize (D.weight pinned)) (oneSiteFibre x σ)) :
    normSq (conditionalSpinMean (normalize (D.weight pinned)) x σ) ≤ (3 / 5 : ℝ)^2 := by
  obtain ⟨k, hk, a, ha, _, hEq⟩ := hReduction n D hD pinned x hPin hDegree σ hMass
  rw [hEq]
  exact (hMean.1 k hk a ha (D.status x) (hD.1 x)).2

/-- `l:exact`, lines 327–331: the degree test for the whole inserted signed
product supplies the quadrature comparison. In particular use coefficients ±1
and unit pin vectors. Lists retain repeated factors and endpoint multiplicities. -/
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
      (fun a => MvPolynomial.eval (fun z => a z.1 z.2) (interactionPolynomial bonds pins p)) := by
  apply quadrature_congruence hExpand productFactorization
  · intro x m hm
    exact (frameOptionSum (k x) (F x) (s x) (hs x) (mono m)).trans
      (hSingle (k x) (F x) (hF x) (s x) (hs x) m hm)
  · exact hDegree n bonds pins p hp

#print axioms moments_of_leaves
#print axioms finiteFacts_of_leaves
#print axioms threeFactorMean_of_leaves
#print axioms exact_of_leaves
#print axioms all_of_leaves
#print axioms conditional_threeFactorMean_of_leaves
#print axioms interaction_exact_of_leaves

end AKLT.Blueprint.Mom
