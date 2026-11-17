module
public import AKLT.Blueprint.Q.NodesFrames
public import AKLT.Blueprint.Q.NodesTight
public import AKLT.Blueprint.Q.NodesStar
public import AKLT.Blueprint.Q.NodesPolynomial
public import AKLT.Blueprint.Q.NodesQuantum
public import AKLT.Blueprint.Q.NodesEnergy
public import AKLT.Blueprint.Q.NodesSplits

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-! Checked implications only. Every mathematical argument to an exported
assembly is a closed proposition. Generic leaf premises are ordinary explicit
finite mathematical data/equations, never names of other open leaves. -/

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Challenge

namespace AKLT.Blueprint.Q

theorem threeFrames_of_leaves (hMom : Top.MomentsStatement)
    (hFamily : OrthogonalFamilyStatement) (hEncoding : OneSiteMomentEncodingStatement)
    (hDistance : IcoDistanceStatement) (hDisplacement : RotationDisplacementStatement)
    (hSelf : SelfRotationStatement) (hMetric : DisplacedDistanceStatement)
    (hRelative : RelativeRotationStatement) : Top.ThreeFramesStatement := by
  classical
  rcases frameScalars with ⟨hb, hb1, hb9, hr, hr1, _, _⟩
  have hGeometry := fun j : Fin 3 =>
    hFamily (frameRotation ^ j.val) (rotationPowers j) icoVector
      hMom.1 hMom.2.1 hMom.2.2.1
  have hCov : ∀ R : Matrix (Fin 3) (Fin 3) ℝ, R.transpose * R = 1 →
      ∀ p : MvPolynomial (Fin 3) ℝ, DegreeFour p →
        moment (fun a => MvPolynomial.eval (R.mulVec a) p) =
          moment (fun a => MvPolynomial.eval a p) := by
    intro R hR p hp
    obtain ⟨q, hq, hq0, hqR⟩ := hEncoding p hp
    rcases hMom with ⟨_, _, _, _, _, _, _, _, _, hCov⟩
    rw [← hqR R, ← hq0]
    exact hCov 1 (fun _ => .U) (by simp) q hq (fun _ => R) (fun _ => hR)
  have hFrames : ∀ j : Fin 3, Function.Injective (frameVector j) ∧
      (∀ a, normSq (frameVector j a) = 1) ∧
      (∀ a, ∃ b, frameVector j b = -frameVector j a) ∧
      ∀ p : MvPolynomial (Fin 3) ℝ, DegreeFour p →
        (1 / 12 : ℝ) * (∑ a, MvPolynomial.eval (frameVector j a) p) =
          moment (fun a => MvPolynomial.eval a p) := by
    intro j
    refine ⟨(hGeometry j).1, (hGeometry j).2.1, (hGeometry j).2.2, ?_⟩
    intro p hp
    exact hCov (frameRotation ^ j.val) (rotationPowers j) p hp
  have hMinus : ∀ i j : Fin 3, i ≠ j → ∀ a b : IcoLetter,
      frameBound ≤ 1 - dot (frameVector i a) (frameVector j b) := by
    intro i j hij a b
    obtain ⟨k, hk1, hk2, u, v, huv⟩ := hRelative i j hij a b
    rw [huv]
    by_cases he : u = v
    · subst u
      exact hSelf.1 k hk1 hk2 v
    · have hu := hMom.2.1 u
      have hv := hMom.2.1 v
      have hw := (hGeometry (⟨k, by omega⟩ : Fin 3)).2.1 v
      exact le_of_lt (hb9.trans (hMetric (icoVector u) (icoVector v)
        ((frameRotation ^ k).mulVec (icoVector v)) hu hv hw
        (hDistance u v he) (hDisplacement k hk1 hk2 (icoVector v) hv)))
  refine ⟨rotation.1, rotation.2, hb, hb1, hr, hr1, hFrames, ?_, ?_⟩
  · intro i j hij a b
    have hm := hMinus i j hij a b
    obtain ⟨b', hb'⟩ := (hFrames j).2.2.1 b
    have hp := hMinus i j hij a b'
    have hp' : frameBound ≤ 1 + dot (frameVector i a) (frameVector j b) := by
      simpa [hb', dot, Finset.sum_neg_distrib] using hp
    refine ⟨hp', by linarith, hm, by linarith, ?_, ?_⟩
    · intro he
      have hd : dot (frameVector i a) (frameVector j b) = 1 := by
        rw [he]
        exact (hFrames j).2.1 b
      linarith
    · intro he
      have hd : dot (frameVector i a) (frameVector j b) = -1 := by
        rw [he]
        simpa [normSq, dot, Finset.sum_neg_distrib] using congrArg Neg.neg ((hFrames j).2.1 b)
      linarith
  · exact ⟨0, 1, by decide, (0, 0, 0), (0, 0, 0), hSelf.2⟩

theorem resolution_of_leaves (hDegree : QuarticKernelDegreeStatement)
    (hEval : QuarticKernelEvaluationStatement) (hComplex : ComplexQuadratureStatement)
    (hOff : QuarticOffDiagonalStatement) (hDiag : QuarticDiagonalStatement) :
    ∀ (A : Type) [Fintype A], ∀ v : A → Vec3, ∀ w : A → ℝ,
      quadrature v w → ∀ z : A → Spinor, (∀ a, compatible (v a) (z a)) → resolution w z := by
  intro A _ v w hQuad z hz j k
  have hm : 5 * complexMoment (quarticKernel j k) =
      if j = k then (Nat.choose 4 j.val : ℂ)⁻¹ else 0 := by
    by_cases hjk : j = k
    · subst k
      simpa using hDiag j
    · simp [hjk, hOff j k hjk]
  calc
    (∑ a, (5 * w a : ℂ) * star (quarticMonomial j (z a)) * quarticMonomial k (z a)) =
        ∑ a, (5 : ℂ) * ((w a : ℂ) *
          MvPolynomial.eval (fun i => (v a i : ℂ)) (quarticKernel j k)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [← hEval (v a) (z a) (hz a) j k]
      ring
    _ = 5 * ∑ a, (w a : ℂ) * MvPolynomial.eval (fun i => (v a i : ℂ)) (quarticKernel j k) :=
      (Finset.mul_sum ..).symm
    _ = 5 * complexMoment (quarticKernel j k) := by rw [hComplex A v w hQuad _ (hDegree j k)]
    _ = _ := hm

theorem tight_of_leaves (hThree : Top.ThreeFramesStatement)
    (hChoice : SpinorChoiceStatement) (hDegree : QuarticKernelDegreeStatement)
    (hEval : QuarticKernelEvaluationStatement) (hComplex : ComplexQuadratureStatement)
    (hOff : QuarticOffDiagonalStatement) (hDiag : QuarticDiagonalStatement)
    (hExpansion : ResolutionExpansionStatement) (hTensor : TensorResolutionStatement) :
    Top.TightStatement := by
  classical
  rcases hThree with ⟨_, _, _, _, _, _, hFrames, _, _⟩
  have hSpin : ∀ j a, compatible (frameVector j a) (frameSpinor j a) :=
    fun j a => hChoice _ ((hFrames j).2.1 a)
  have hRes := resolution_of_leaves hDegree hEval hComplex hOff hDiag
  have hFrozenRes : ∀ j : Fin 3, resolution (fun _ : IcoLetter => (1 / 12 : ℝ)) (frameSpinor j) := by
    intro j
    apply hRes IcoLetter (frameVector j) (fun _ => 1 / 12) _ (frameSpinor j) (hSpin j)
    intro p hp
    simpa [← Finset.mul_sum] using (hFrames j).2.2.2 p hp
  refine ⟨hSpin, ?_, ?_, ?_⟩
  · intro n F hF z hz p
    exact hExpansion (Fin n) F.weight z
      (hRes (Fin n) F.point F.weight hF.2.2.2.2 z hz) p
  · intro L N κ ψ
    simpa [torusReference, frameEval, div_eq_mul_inv, mul_pow] using
      hTensor L N (fun _ => IcoLetter) (fun _ => inferInstance)
        (fun _ _ => (1 / 12 : ℝ)) (fun x => frameSpinor (κ x)) (fun x => hFrozenRes (κ x)) ψ
  · intro L N k F hF z hz ψ
    exact hTensor L N (fun x => Fin (k x)) (fun _ => inferInstance)
      (fun x => (F x).weight) z
      (fun x => hRes (Fin (k x)) (F x).point (F x).weight (hF x).2.2.2.2 (z x) (hz x)) ψ

theorem star_of_leaves (hKernel : Top.TorusKernelStatement)
    (hPositive : StarPositiveStatement) (hWitness : StarWitnessStatement)
    (hMinimum : PositiveSpectralMinimumStatement) (hCoercive : SpectralKernelCoercivityStatement)
    (hRelabel : StarRelabellingStatement) (hAmplify : StarAmplificationStatement) :
    Top.StarStatement := by
  obtain ⟨hg, hEigen, hLeast⟩ := hMinimum (Fin 5 → Fin 5) starHamiltonian
    hPositive.1 hPositive.2 ⟨4, by norm_num, hWitness⟩
  have hStar := hCoercive (Fin 5 → Fin 5) starHamiltonian hPositive.1 hPositive.2 starGap hg hLeast
  refine ⟨hg, hEigen, hLeast, ?_⟩
  intro L N
  refine ⟨incidentDoubleCount L N (hKernel L N).1, ?_⟩
  intro x
  obtain ⟨n, U, hU⟩ := hRelabel L N x
  exact hAmplify (Configuration L N) (siteHamiltonian x) n U hU starGap hStar

theorem density_poincare_of_leaves (hVar : DensityVarianceStatement)
    (hDir : DensityDirichletStatement) :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι], ∀ S : ι → Type,
      ∀ (_ : ∀ x, Fintype (S x)), ∀ p q : Weight ((x : ι) → S x),
        PositiveProbability p → PositiveProbability q → PoincareLower p 1 →
        ∀ m M : ℝ, 0 < m → 0 < M →
          (∀ σ, m * p σ ≤ q σ) → (∀ σ, q σ ≤ M * p σ) → PoincareLower q (m / M) := by
  intro ι _ _ S _ p q hp hq hg m M hm hM hlo hhi f
  have hv := hVar _ p q hp hq M hM.le hhi f
  have hd := hDir ι S inferInstance p q hp hq m hm.le hlo f
  have hg' : variance p f ≤ dirichlet p f := by simpa using hg f
  calc
    (m / M) * variance q f ≤ (m / M) * (M * variance p f) :=
      mul_le_mul_of_nonneg_left hv (div_nonneg hm.le hM.le)
    _ = m * variance p f := by field_simp
    _ ≤ m * dirichlet p f := mul_le_mul_of_nonneg_left hg' hm.le
    _ ≤ dirichlet q f := hd

theorem planeEnergy_of_leaves (hThree : Top.ThreeFramesStatement)
    (hWeights : FrameWeightsPositiveStatement)
    (hCondition : PlaneConditioningStatement) (hMarkov : TorusMarkovStatement)
    (hPlaneSite : PlaneOneSiteEnergyStatement) (hTorusSite : TorusOneSiteEnergyStatement)
    (hPartial : PartialAssignmentStatement) (hReindex : PlaneAssignmentReindexStatement)
    (hReference : PlaneProductReferenceStatement) (hAbsorb : BoundaryAbsorptionStatement)
    (hBounds : PlaneDensityBoundsStatement) (hVar : DensityVarianceStatement)
    (hDir : DensityDirichletStatement) (hProduct : ProductPoincareStatement) :
    Top.PlaneEnergyStatement := by
  classical
  have hBoundsData : interactionBounds := by
    rcases hThree with ⟨_, _, _, _, _, _, _, hSep, _⟩
    intro i j hij a b
    obtain ⟨h1, h2, h3, h4, _, _⟩ := hSep i j hij a b
    exact ⟨h1, h2, h3, h4⟩
  have hWeights := hWeights hBoundsData
  have hCondition := hCondition hBoundsData
  have hMarkov := hMarkov hBoundsData
  have hPlaneSite := hPlaneSite hBoundsData
  have hTorusSite := hTorusSite hBoundsData
  have hReference := hReference hBoundsData
  have hAbsorb := hAbsorb hBoundsData
  have hBounds := hBounds hBoundsData
  rcases frameScalars with ⟨_, _, _, _, _, he, he1⟩
  refine ⟨he, he1, ?_, ?_⟩
  · intro κ hκ W η
    have hp : PositiveProbability (planeLaw κ W η) :=
      positiveNormalization _ _ (hWeights.1 κ hκ W η)
    have hPart := hPartial W (fun _ => IcoLetter) (fun _ => inferInstance)
      (fun _ => inferInstance) (planeLaw κ W η) hp frameEnergy he he1 (hPlaneSite κ hκ W η)
    refine ⟨hp, hCondition κ hκ W η, hReindex W _ frameEnergy hPart, ?_⟩
    have hRef := hReference κ hκ W η
    obtain ⟨_, hm, hM, hlo, hhi, hratio⟩ := hBounds κ hκ W η hRef.2 (hAbsorb κ hκ W η)
    have hg : PoincareLower (planeProductReference κ W η) 1 :=
      hProduct W (fun _ => IcoLetter) (fun _ => inferInstance)
        (fun x => normalize (planeSiteWeight κ W η x)) hRef.1
    rw [← hratio]
    exact density_poincare_of_leaves hVar hDir W (fun _ => IcoLetter) (fun _ => inferInstance)
      _ _ hRef.2 hp hg _ _ hm hM hlo hhi
  · intro L N κ hκ
    have hp : PositiveProbability (torusLaw L N κ) :=
      positiveNormalization _ _ (hWeights.2 L N κ hκ)
    exact ⟨hp, hMarkov L N κ hκ,
      hPartial (Site L N) (fun _ => IcoLetter) (fun _ => inferInstance)
        (fun _ => inferInstance) (torusLaw L N κ) hp frameEnergy he he1 (hTorusSite L N κ hκ)⟩

theorem localKernelFactorization_of_leaves (hPair : PairSpinFourStatement)
    (hDivision : PairDiagonalDivisionStatement) (hSpectator : SpectatorDivisibilityStatement)
    (hPrime : SingletPrimeStatement) (hNonassoc : SingletNonassociateStatement)
    (hProduct : PrimeProductStatement) (hIncident : IncidentKernelStatement)
    (hDegree : IncidentDegreeStatement) :
    ∀ L N : Size, ∀ x : Site L N, ∀ ψ : Hilbert L N,
      siteHamiltonian x ψ = 0 → ∃ χ : SpinorPolynomial L N,
        statePolynomial ψ = incidentProduct x * χ ∧ independentAt x χ := by
  classical
  have hPairKernel : ∀ v : PairHilbert, pairProjector v = 0 → pairSinglet ∣ pairPolynomial v := by
    intro v hv
    apply hDivision v
    change (Module.End.eigenspace pairCasimir 20).starProjection v = 0 at hv
    rw [show Module.End.eigenspace pairCasimir 20 = (LinearMap.ker pairDiagonal)ᗮ from hPair] at hv
    have hm := (Submodule.starProjection_apply_eq_zero_iff (LinearMap.ker pairDiagonal)ᗮ).mp hv
    simpa [Submodule.orthogonal_orthogonal] using hm
  intro L N x ψ hψ
  let I := {e : Bond L N // x ∈ bondSites e}
  have hd : (∏ e : I, singlet e.val) ∣ statePolynomial ψ := by
    apply hProduct I (SpinorPolynomial L N) (fun e => singlet e.val)
    · exact fun e => hPrime L N e.val
    · intro e f hef
      exact hNonassoc L N e.val f.val (fun h => hef (Subtype.ext h))
    · intro e
      exact hSpectator hPairKernel L N e.val ψ (hIncident L N x ψ hψ e.val e.property)
  have hprod : (∏ e : I, singlet e.val) = incidentProduct x := by
    dsimp [I, incidentProduct]
    rw [← Finset.prod_filter]
    exact (Finset.prod_subtype _ (by simp) singlet).symm
  rw [hprod] at hd
  obtain ⟨χ, hχ⟩ := hd
  exact ⟨χ, hχ, hDegree L N x ψ χ hχ⟩

theorem groundEvaluation_of_leaves (hEval : StateEvaluationStatement)
    (hHom : VbsHomogeneityStatement) (hReconstruct : CoefficientReconstructionStatement) :
    ∀ L N : Size, ∀ κ : Site L N → Fin 3, ∀ σ : TorusConfiguration L N,
      frameEval κ (B L N) σ = ∏ e : Bond L N,
        determinant (frameSpinor (κ e.1) (σ e.1))
          (frameSpinor (κ (nextSite e.1 e.2)) (σ (nextSite e.1 e.2))) := by
  intro L N κ σ
  have hState : statePolynomial (B L N) = vbsPolynomial L N :=
    hReconstruct L N (vbsPolynomial L N) (hHom L N)
  unfold frameEval
  rw [← hEval L N (B L N), hState]
  simp [vbsPolynomial, singlet, determinant]

theorem normalize_from_scaled :
    ∀ (Ω : Type) [Fintype Ω], ∀ w r : Weight Ω, ∀ c n : ℝ,
      0 < c → 0 < n → (∀ σ, r σ = c * w σ) → (∑ σ, r σ) = n →
        AKLT.Defs.normalize w = fun σ => r σ / n := by
  intro Ω _ w r c n hc hn hr hs
  have hsum : n = c * ∑ σ, w σ := by rw [← hs]; simp_rw [hr]; rw [Finset.mul_sum]
  have hw : (∑ σ, w σ) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hsum
    exact hn.ne' hsum
  funext σ
  apply (div_eq_div_iff hw hn.ne').2
  rw [hr, hsum]
  ring

theorem qd_of_leaves (hThree : Top.ThreeFramesStatement) (hTight : Top.TightStatement)
    (hStar : Top.StarStatement) (hKernel : Top.TorusKernelStatement)
    (hEval : StateEvaluationStatement) (hHom : VbsHomogeneityStatement)
    (hReconstruct : CoefficientReconstructionStatement) (hPair : PairSpinFourStatement)
    (hDivision : PairDiagonalDivisionStatement) (hSpectator : SpectatorDivisibilityStatement)
    (hPrime : SingletPrimeStatement) (hNonassoc : SingletNonassociateStatement)
    (hProduct : PrimeProductStatement) (hIncident : IncidentKernelStatement)
    (hDegree : IncidentDegreeStatement) (hModulus : DeterminantModulusStatement)
    (hWeight : GroundProductWeightStatement) (hLocalEval : IncidentEvaluationStatement)
    (hFactor : GroundFibreFactorizationStatement) (hTransform : GroundTransformStatement)
    (hIntertwine : FibreIntertwiningStatement) (hProjection : FibreProjectionStatement)
    (hPolar : WeightedPolarizationStatement) (hVariance : GroundQuotientVarianceStatement)
    (hBeta : BetaNonzeroStatement) : Top.QDStatement := by
  classical
  intro L N κ hκ
  rcases hThree with ⟨_, _, hb, _, _, _, _, hSeparation, _⟩
  have hSpin := hTight.1
  have hGround := groundEvaluation_of_leaves hEval hHom hReconstruct L N κ
  have hqmod := fun e : Bond L N => fun σ : TorusConfiguration L N =>
    hModulus _ _ _ _ (hSpin (κ e.1) (σ e.1))
      (hSpin (κ (nextSite e.1 e.2)) (σ (nextSite e.1 e.2)))
  have hqpos : ∀ e : Bond L N, ∀ σ : TorusConfiguration L N,
      0 < Complex.normSq (determinant (frameSpinor (κ e.1) (σ e.1))
        (frameSpinor (κ (nextSite e.1 e.2)) (σ (nextSite e.1 e.2)))) := by
    intro e σ
    rw [hqmod]
    have hbound := (hSeparation _ _ (hκ e) (σ e.1) (σ (nextSite e.1 e.2))).2.2.1
    exact div_pos (hb.trans_le hbound) (by norm_num)
  have hGroundNonzero : ∀ σ, frameEval κ (B L N) σ ≠ 0 := by
    intro σ
    rw [hGround σ]
    apply Finset.prod_ne_zero_iff.mpr
    intro e _ hz
    have hp := hqpos e σ
    rw [hz] at hp
    norm_num at hp
  have hB : B L N ≠ 0 := (hKernel L N).2.2.2.1
  have hNorm : 0 < ‖B L N‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hB)
  have hRaw := hWeight L N κ hGround hqmod
  have hSum : (∑ σ, torusReference L N σ * Complex.normSq (frameEval κ (B L N) σ)) =
      ‖B L N‖^2 := hTight.2.2.1 L N κ (B L N)
  have hScale : 0 < groundScale L N := by unfold groundScale; positivity
  have hLaw : ∀ σ, torusLaw L N κ σ = torusReference L N σ *
      Complex.normSq (frameEval κ (B L N) σ) / ‖B L N‖^2 :=
    congrFun (normalize_from_scaled _ _ _ _ _ hScale hNorm hRaw hSum)
  refine ⟨hLaw, ?_⟩
  intro γ hγ ψ hψ
  have hInner := hPolar (Configuration L N) (TorusConfiguration L N) (torusReference L N)
    (coherentMap κ) (hTight.2.2.1 L N κ)
  have hVar := (hVariance L N κ hB hGroundNonzero hLaw hInner ψ hψ).2
  have hInv := (hTransform L N κ hB hGroundNonzero hLaw).2.1 ψ
  have hFact := hFactor L N κ hGround
  have hBet := hBeta L N κ hqpos
  have hLocal := localKernelFactorization_of_leaves hPair hDivision hSpectator
    hPrime hNonassoc hProduct hIncident hDegree L N
  have hDist : ∀ x : Site L N,
      blockDirichlet (torusLaw L N κ) {x} (groundQuotient κ ψ) ≤
        ‖ψ - (LinearMap.ker (siteHamiltonian x)).starProjection ψ‖^2 := by
    intro x
    have hTransport := (hIntertwine L N κ x hB (hBet x) (hFact x).1 (hFact x).2
      hLaw hGroundNonzero).2 (groundQuotient κ ψ)
    rw [hInv] at hTransport
    rw [hTransport]
    let φ := (LinearMap.ker (siteHamiltonian x)).starProjection ψ
    have hφ : siteHamiltonian x φ = 0 :=
      (Submodule.starProjection_apply_mem (LinearMap.ker (siteHamiltonian x)) ψ)
    obtain ⟨χ, hχ, hIndependent⟩ := hLocal x φ hφ
    have hSpan := (hLocalEval L N κ x φ χ hχ hIndependent).2
    have hBest := (hProjection L N κ x (hBet x)).2.2.2 (frameEval κ ψ) (frameEval κ φ) hSpan
    have hIso : weightedNorm (torusReference L N) (frameEval κ ψ - frameEval κ φ) = ‖ψ - φ‖^2 := by
      change weightedNorm (torusReference L N) ((coherentMap κ) ψ - (coherentMap κ) φ) = ‖ψ - φ‖^2
      rw [← (coherentMap κ).map_sub]
      exact hTight.2.2.1 L N κ (ψ - φ)
    exact hBest.trans_eq hIso
  have hClass : γ * ‖ψ‖^2 ≤
      ∑ x : Site L N, ‖ψ - (LinearMap.ker (siteHamiltonian x)).starProjection ψ‖^2 := by
    calc
      γ * ‖ψ‖^2 = γ * variance (torusLaw L N κ) (groundQuotient κ ψ) := by rw [hVar]
      _ ≤ dirichlet (torusLaw L N κ) (groundQuotient κ ψ) := hγ _
      _ ≤ _ := Finset.sum_le_sum (fun x _ => hDist x)
  have hQuantum : starGap *
      (∑ x : Site L N, ‖ψ - (LinearMap.ker (siteHamiltonian x)).starProjection ψ‖^2) ≤
        2 * (inner ℂ ψ (H L N ψ)).re := by
    calc
      _ = ∑ x : Site L N,
          starGap * ‖ψ - (LinearMap.ker (siteHamiltonian x)).starProjection ψ‖^2 := Finset.mul_sum ..
      _ ≤ ∑ x : Site L N, (inner ℂ ψ (siteHamiltonian x ψ)).re :=
        Finset.sum_le_sum (fun x _ => (hStar.2.2.2 L N).2 x ψ)
      _ = 2 * (inner ℂ ψ (H L N ψ)).re := by
        rw [← Complex.re_sum, ← inner_sum, ← LinearMap.sum_apply, (hStar.2.2.2 L N).1]
        simp [two_smul, inner_add_right, two_mul]
  have hMultiply := mul_le_mul_of_nonneg_left hClass hStar.1.le
  nlinarith

theorem pairSpinFour_of_leaves (hRank : PairDiagonalRankStatement)
    (hInclusion : PairTopInclusionStatement) (hDimension : PairTopDimensionStatement) :
    PairSpinFourStatement := by
  apply Eq.symm
  apply Submodule.eq_of_le_of_finrank_eq hInclusion
  have h := (LinearMap.ker pairDiagonal).finrank_add_finrank_orthogonal
  have hTotal : Module.finrank ℂ PairHilbert = 25 := by simp [PairHilbert]
  change Module.finrank ℂ (LinearMap.ker pairDiagonal) = 16 at hRank
  change Module.finrank ℂ (Module.End.eigenspace pairCasimir 20) = 9 at hDimension
  omega

theorem singletPrime_of_leaves (hFour : FourVariableDeterminantPrimeStatement)
    (hEmbed : DeterminantPrimeEmbeddingStatement) : SingletPrimeStatement := hEmbed hFour

theorem incidentDegree_of_leaves (hCancellation : CentreDegreeCancellationStatement)
    (hProduct : IncidentProductDegreeStatement) (hState : StateCentreDegreeStatement) :
    IncidentDegreeStatement := by
  intro L N x ψ χ hχ
  apply hCancellation L N x (incidentProduct x) χ (hProduct L N x).1 (hProduct L N x).2
  rw [← hχ]
  exact hState L N ψ x

theorem starRelabelling_of_leaves (hEnumeration : StarEdgeEnumerationStatement)
    (hChart : StarCasimirChartStatement) (hTransport : StarProjectorTransportStatement) :
    StarRelabellingStatement := by
  classical
  intro L N x
  obtain ⟨n, U, hU⟩ := hChart L N x
  refine ⟨n, U, ?_⟩
  have hs : siteHamiltonian x = ∑ j : Fin 4, P (starEdge x j) := by
    unfold siteHamiltonian
    rw [← Finset.sum_filter, ← (hEnumeration L N x).2,
      Finset.sum_image (hEnumeration L N x).1.injOn]
  intro ψ r s
  calc
    U (siteHamiltonian x ψ) (r, s) = ∑ j : Fin 4, U (P (starEdge x j) ψ) (r, s) := by
      rw [hs]
      simp [LinearMap.sum_apply]
    _ = ∑ j : Fin 4, (Module.End.eigenspace (starCasimir j) 20).starProjection
          (WithLp.toLp 2 (fun t => U ψ (r, t))) s := by
      apply Finset.sum_congr rfl
      intro j _
      exact hTransport L N x n U hU j ψ r s
    _ = starHamiltonian (WithLp.toLp 2 (fun t => U ψ (r, t))) s := by
      simp [starHamiltonian, LinearMap.sum_apply]

/-- Bundles are conjunctions for orchestration, not additional open leaves. -/
def FramesInputs : Prop := OrthogonalFamilyStatement ∧ OneSiteMomentEncodingStatement ∧
  IcoDistanceStatement ∧ RotationDisplacementStatement ∧ SelfRotationStatement ∧
  DisplacedDistanceStatement ∧ RelativeRotationStatement

def TightInputs : Prop := SpinorChoiceStatement ∧ QuarticKernelDegreeStatement ∧
  QuarticKernelEvaluationStatement ∧ ComplexQuadratureStatement ∧ QuarticOffDiagonalStatement ∧
  QuarticDiagonalStatement ∧ ResolutionExpansionStatement ∧ TensorResolutionStatement

def StarInputs : Prop := StarPositiveStatement ∧ StarWitnessStatement ∧
  PositiveSpectralMinimumStatement ∧ SpectralKernelCoercivityStatement ∧ StarAmplificationStatement ∧
  StarEdgeEnumerationStatement ∧ StarCasimirChartStatement ∧ StarProjectorTransportStatement

def PolynomialInputs : Prop := StateEvaluationStatement ∧ VbsHomogeneityStatement ∧
  CoefficientReconstructionStatement ∧ PairDiagonalDivisionStatement ∧ SpectatorDivisibilityStatement ∧
  SingletNonassociateStatement ∧ IncidentKernelStatement ∧
  PairDiagonalRankStatement ∧ PairTopInclusionStatement ∧ PairTopDimensionStatement ∧
  FourVariableDeterminantPrimeStatement ∧ DeterminantPrimeEmbeddingStatement ∧
  CentreDegreeCancellationStatement ∧ IncidentProductDegreeStatement ∧ StateCentreDegreeStatement

def QuantumInputs : Prop := DeterminantModulusStatement ∧ GroundProductWeightStatement ∧
  IncidentEvaluationStatement ∧ GroundFibreFactorizationStatement ∧ GroundTransformStatement ∧
  FibreIntertwiningStatement ∧ FibreProjectionStatement ∧ WeightedPolarizationStatement ∧
  GroundQuotientVarianceStatement ∧ BetaNonzeroStatement

def EnergyInputs : Prop := FrameWeightsPositiveStatement ∧ PlaneConditioningStatement ∧
  TorusMarkovStatement ∧ PlaneOneSiteEnergyStatement ∧ TorusOneSiteEnergyStatement ∧
  PartialAssignmentStatement ∧ PlaneAssignmentReindexStatement ∧ PlaneProductReferenceStatement ∧
  BoundaryAbsorptionStatement ∧ PlaneDensityBoundsStatement ∧ DensityVarianceStatement ∧
  DensityDirichletStatement ∧ ProductPoincareStatement

/-- Complete acyclic assembly of the assigned five targets. The only external
part inputs are l:moments and p:toruskernel. Each remaining input is a bundle
of the exact open leaves listed in the report manifest. -/
theorem allTargets_of_leaves (hMom : Top.MomentsStatement) (hKernel : Top.TorusKernelStatement)
    (hFrames : FramesInputs) (hTight : TightInputs) (hStar : StarInputs)
    (hPoly : PolynomialInputs) (hQuantum : QuantumInputs) (hEnergy : EnergyInputs) :
    Top.ThreeFramesStatement ∧ Top.TightStatement ∧ Top.StarStatement ∧
      Top.QDStatement ∧ Top.PlaneEnergyStatement := by
  rcases hFrames with ⟨f1, f2, f3, f4, f5, f6, f7⟩
  have hThree := threeFrames_of_leaves hMom f1 f2 f3 f4 f5 f6 f7
  rcases hTight with ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩
  have hTight' := tight_of_leaves hThree t1 t2 t3 t4 t5 t6 t7 t8
  rcases hStar with ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩
  have hStar' := star_of_leaves hKernel s1 s2 s3 s4 (starRelabelling_of_leaves s6 s7 s8) s5
  rcases hPoly with ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15⟩
  rcases hQuantum with ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10⟩
  have hQD := qd_of_leaves hThree hTight' hStar' hKernel p1 p2 p3
    (pairSpinFour_of_leaves p8 p9 p10) p4 p5 (singletPrime_of_leaves p11 p12) p6 primeProduct p7
    (incidentDegree_of_leaves p13 p14 p15) q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  rcases hEnergy with ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13⟩
  exact ⟨hThree, hTight', hStar', hQD,
    planeEnergy_of_leaves hThree e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13⟩

end AKLT.Blueprint.Q
