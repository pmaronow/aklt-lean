import AKLT.Blueprint.Gap.NodesMain

/-! Kernel-checked logical assembly only. Every unproved input argument is a closed
Prop defined in a Nodes module or an unchanged Top module. -/

noncomputable section
set_option maxHeartbeats 500000
open scoped BigOperators
open AKLT.Defs AKLT.Challenge AKLT.Blueprint.Top
attribute [local instance] Classical.propDecidable
namespace AKLT.Blueprint.Gap
local instance (α : Type) : DecidableEq α := Classical.decEq α

/-- Split the spectral step a second time: the Lipschitz eigenvalue estimate is
independent of the weighted diagonalization and complex quadratic-form argument. -/
theorem reversibleSpectral_of_parts (hEigen : LipschitzEigenvalueStatement)
    (hGap : ReversibleEigenvalueGapStatement) : ReversibleSpectralStatement := by
  intro ι _ _ S _ _ p K hp hRev A c hA hc hcA hLip
  have hr : 0 ≤ 1-c/A := sub_nonneg.mpr ((div_le_one hA).mpr hcA)
  exact hGap ι S p K hp hRev A c hA hc hcA (hEigen ι S p K hp (1-c/A) hr hLip)

/-- Appendix l:contraction, assembled from the finite kernel, Lipschitz, and spectral
obligations. The output is an implication and certifies none of its open inputs. -/
theorem finiteContraction_of_parts
    (hForm : BlockAverageFormStatement) (hLip : LipschitzCouplingStatement)
    (hSpec : ReversibleSpectralStatement) : FiniteContractionStatement := by
  intro ι J _ _ _ _ S _ _ p hp B c hc hcA hCouple
  obtain ⟨hRev, hEnergy⟩ := hForm ι J S p hp B
  have hA : (0 : ℝ) < Fintype.card J := Nat.cast_pos.mpr Fintype.card_pos
  have hr : 0 ≤ 1-c/(Fintype.card J : ℝ) := by
    apply sub_nonneg.mpr
    exact (div_le_one hA).mpr hcA
  have hL := hLip ι S (blockAverage p B) hRev.1 (1-c/Fintype.card J) hr hCouple
  have hSpectral := hSpec ι S p (blockAverage p B) hp hRev
    (Fintype.card J) c hA hc hcA hL
  intro f
  exact (hSpectral f).trans_eq (hEnergy f)

/-- Appendix l:comparison: integrate fibre inequalities and divide only by t>0. -/
theorem blockComparison_of_parts (hCond : ConditionalBlockComparisonStatement)
    (hMult : MultiplicityEstimateStatement) : BlockComparisonStatement := by
  intro ι J _ _ _ S _ _ p hp B t g c ht hg hc hCount hBlocks hGap f
  have h₁ := hCond ι J S p hp B g hg hBlocks f
  have h₂ := hMult ι J S p hp B t hCount f
  have h₃ := mul_le_mul_of_nonneg_left (hGap f) hg.le
  have htR : (0 : ℝ) < t := Nat.cast_pos.mpr ht
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ htR).mpr
  nlinarith

/-- t:periodic, including the exact block gap before division by block multiplicity. -/
theorem periodicCriterion_of_parts
    (hInside : ContainingBlockCountStatement) (hOutside : ExteriorBlockCountStatement)
    (hVolume : BlockVolumeBoundStatement) (hNeighbour : PeriodicNeighbourCouplingStatement)
    (hContract : FiniteContractionStatement) (hCompare : BlockComparisonStatement) :
    PeriodicCriterionStatement := by
  intro L N S _ _ μ hμ M g K hM hL hN hg hK hRange hBlocks hInfluence hStrict
  have hCounts : PeriodicCounts L N M :=
    ⟨hInside L N M hM hL hN, hOutside L N M hM hL hN, hVolume L N M hM hL hN⟩
  have ht : 0 < volumeCount M := by unfold volumeCount; positivity
  have htR : (0 : ℝ) < volumeCount M := Nat.cast_pos.mpr ht
  have hc : 0 < (volumeCount M : ℝ)-(haloCount M : ℝ)*K := sub_pos.mpr hStrict
  have hcA : (volumeCount M : ℝ)-(haloCount M : ℝ)*K ≤ Fintype.card (Site L N) := by
    have hT : (volumeCount M : ℝ) ≤ Fintype.card (Site L N) := by exact_mod_cast hCounts.2.2
    have hS : (0 : ℝ) ≤ haloCount M := Nat.cast_nonneg _
    nlinarith
  have hGap := hContract (Site L N) (Site L N) S μ hμ (torusSquare L N M)
    ((volumeCount M : ℝ)-(haloCount M : ℝ)*K) hc hcA
    (hNeighbour L N S μ hμ M K hM hK hCounts hRange hInfluence)
  refine ⟨hGap, ?_⟩
  have hSingle := hCompare (Site L N) (Site L N) S μ hμ (torusSquare L N M)
    (volumeCount M) g ((volumeCount M : ℝ)-(haloCount M : ℝ)*K) ht hg hc
    (fun x => (hCounts.1 x).le) hBlocks hGap
  have hCoeff : (((volumeCount M : ℝ)-(haloCount M : ℝ)*K)*g/(volumeCount M : ℝ)) =
      g*(1-(haloCount M : ℝ)*K/(volumeCount M : ℝ)) := by field_simp
  rw [hCoeff] at hSingle
  exact hSingle

/-- The pointwise rows assemble by finite choice; no extra mathematical input is used. -/
theorem stoppedCoupling_of_parts
    (hRows : ShellRowStatement) (hTrace : TraceMarginalsStatement)
    (hCount : TrialCountStatement) (hAbsorb : ShellAbsorptionStatement)
    (hFailure : FiniteTrialFailureStatement) (hEndpoint : TraceDisagreementStatement)
    (hSpacing : ThresholdSpacingStatement) (hGeometry : ShellGeometryStatement) :
    StoppedCouplingStatement := by
  intro P hP l p Mstar α hα hα1 hEnergy hW a u hu y hy η ξ hηξ h hh hs
  have hLocal : ShellGeometry l a y u := by
    obtain ⟨h₀, h₁, h₂, h₃⟩ := hGeometry l hW.1 a y u ((le_max_right _ _).trans hu) hy
    exact ⟨h₀, h₁, fun i hi hi1 hi0 => (h₂ i hi hi1 hi0).1, h₃⟩
  have hrows := hRows P hP l p Mstar α hα hα1 hEnergy hW a u hu y hy hLocal η ξ hηξ h hh hs
  choose row hrow using hrows
  let R : SurgeryKernels P a y u l h p α η ξ := {
    kernel := row
    stochastic := fun j ω => (hrow j ω).1
    marginals := fun j ω => (hrow j ω).2.1
    fixed_exterior := fun j ω => (hrow j ω).2.2.1
    identical := fun j ω => (hrow j ω).2.2.2.1
    success := fun j ω => (hrow j ω).2.2.2.2 }
  obtain ⟨hProb, c, hc⟩ := hTrace P hP a y u l h p α η ξ R
  have hδ := deltaBounds l p α hW.2.2.1 hW.2.2.2.1 hα hα1
  have hInit := independentPairsProbability _ _ _
    (positiveToProbability _ _ (hP.1 (square a u) η))
    (positiveToProbability _ _ (hP.1 (square a u) ξ))
  have hFail := hFailure (PlaneConfig P (square a u)) h _ hInit R.kernel R.stochastic
    (trialTimes a y u h) (shellAgreement P a y u h) (p*α^(16*l)) hδ.1.le hδ.2.1 (by
      intro j hj ω
      have hj' := (Finset.mem_filter.mp hj).2
      exact R.success j ω hj'.1 hj'.2.1)
  have hEnd := hEndpoint (square a u) (fun x => P.Letter x.val) h
    (surgeryTrace P a y u l h p α η ξ R) hProb _ _ c hc
    (farSites a y u ((h : ℝ)*shellSpacing u)) (trialTimes a y u h) (shellAgreement P a y u h)
    (hAbsorb P a y u l h p α η ξ (hSpacing l u ((le_max_right _ _).trans hu)) R)
  refine ⟨c, hEnd.trans (hFail.trans ?_)⟩
  exact powerCount _ (sub_nonneg.mpr hδ.2.1) (by linarith [hδ.1]) _ _
    (hCount a y u h hh hLocal.1)

/-- l:hamming at one scale; the far-site case uses the proved diagonal coupling. -/
theorem hammingAtScale_of_parts (hStopped : StoppedCouplingStatement)
    (hScale : ScaleGeometryStatement) (hTail : BinomialTailStatement)
    (hCard : HammingCardinalityStatement) (hBudget : HammingBudgetStatement)
    (hConvert : StoppedHammingConversionStatement) (hFar : FarBoundaryEqualityStatement) :
    HammingAtScaleStatement := by
  intro P hP l p Mstar α hα hα1 hEnergy hW n hn
  have hδ := deltaBounds l p α hW.2.2.1 hW.2.2.2.1 hα hα1
  let d := min (1/2 : ℝ) (p*α^(16*l))
  have hd : 0 < d := hδ.2.2.1
  obtain ⟨hSize, hn4, hIndex, hRadius, _⟩ := hScale l Mstar d n hn
  have htail := hTail d hd hδ.2.2.2.1 n hn.1
  have hbudget := hBudget l Mstar d n hd hδ.2.2.2.1 hn htail
  intro a y hy η ξ hηξ
  by_cases hdist : setDistance supDist y (↑(square a (n^8)) : Set Plane) = 1
  · obtain ⟨c, hc⟩ := hConvert P l p Mstar α n d hd.le hδ.2.2.2.2 hδ.2.1
      hSize hn4 hIndex hRadius (hStopped P hP l p Mstar α hα hα1 hEnergy hW)
      (fun a y => hCard a y n (by omega))
      (fun a η => positiveToProbability _ _ (hP.1 _ _)) a y hdist η ξ hηξ
    exact ⟨c, hc.trans hbudget⟩
  · have heq := hFar P hP a (n^8) y hy hdist η ξ hηξ
    obtain ⟨c, hc⟩ := diagonalCoupling (square a (n^8)) (fun x => P.Letter x.val)
      (P.law (square a (n^8)) η) (positiveToProbability _ _ (hP.1 _ _))
    rw [← heq]
    exact ⟨c, by rw [hc]; positivity⟩

#print axioms finiteContraction_of_parts
#print axioms blockComparison_of_parts
#print axioms periodicCriterion_of_parts
#print axioms stoppedCoupling_of_parts
#print axioms hammingAtScale_of_parts

/-- t:mainW. Choose n before L,N; lift each physical square separately, transport
its gap and Hamming coupling, invoke t:periodic, then QD and the independent kernel.
Only the constants of the paper enter c=(499/1000)g_star g_M and L0=2M+3. -/
theorem mainW_of_core
    (hChoose : ScaleExistenceStatement) (hHamming : HammingAtScaleStatement)
    (hRegular : FrameSpecRegularityStatement) (hEnergyTransfer : FrameSpecEnergyStatement)
    (hWindow : FrameWindowTransferStatement) (hColour : TorusColourStatement)
    (hPullback : PullbackColourStatement) (hInject : HaloInjectionStatement)
    (hBonds : LiftBondStatement) (hCoordinates : BoxCoordinatesStatement)
    (hGauge : BoxGaugeLawStatement) (hRange : TorusRangeTransferStatement)
    (hEdges : SquareInternalEdgesStatement) (hTransportGap : ProductPoincareTransportStatement)
    (hTransportCost : ProductCouplingTransportStatement) (hPeriodic : PeriodicCriterionStatement)
    (hBudget : PeriodicBudgetStatement) (hFrames : ThreeFramesStatement)
    (hStar : StarStatement) (hEnergy : PlaneEnergyStatement) (hQD : QDStatement)
    (hKernel : TorusKernelStatement) : MainWStatement := by
  intro hWitness
  obtain ⟨l, p, Mstar, hW⟩ := hWitness
  rcases hEnergy with ⟨hα, hα1, hPlane, hTorus⟩
  rcases hFrames with ⟨_, _, hb, _, hr, _, hF, hSep, _⟩
  have hδ := deltaBounds l p frameEnergy hW.2.2.1 hW.2.2.2.1 hα hα1
  obtain ⟨n, hn⟩ := hChoose l Mstar (min (1/2) (p*frameEnergy^(16*l))) hδ.2.2.1
  let M := n^8
  have hM : 1 ≤ M := by
    have hn1 : 1 ≤ n := by have := hn.1; omega
    exact one_le_pow₀ hn1
  have hg : 0 < blockGapConstant M := pow_pos hr _
  have hAnti : ∀ j : Fin 3, Function.Injective (frameVector j) ∧
      ∀ a, ∃ b, frameVector j b = -frameVector j a :=
    fun j => ⟨(hF j).1, (hF j).2.2.1⟩
  have hPositive : ∀ i j : Fin 3, i ≠ j → ∀ a b : IcoLetter,
      0 < 1+dot (frameVector i a) (frameVector j b) ∧
      0 < 1-dot (frameVector i a) (frameVector j b) := by
    intro i j hij a b
    exact ⟨hb.trans_le (hSep i j hij a b).1, hb.trans_le (hSep i j hij a b).2.2.1⟩
  refine ⟨(starGap/2)*((499/500)*blockGapConstant M),
    mul_pos (div_pos hStar.1 (by norm_num)) (mul_pos (by norm_num) hg),
    2*M+3, by omega, ?_⟩
  intro L N hL hN
  let κ := torusColour L N
  have hκ : ProperTorusColouring κ := hColour L N
  have hκbar := hPullback L N κ hκ
  have hPlanePos := fun W η => (hPlane (κ ∘ reduction L N) hκbar W η).1
  have hReg : RegularSpec (frameSpec (κ ∘ reduction L N)) :=
    hRegular _ hκbar hPlanePos (fun W V hV η σ => (hPlane _ hκbar W η).2.1 V hV σ)
  have hFE : SpecEnergy (frameSpec (κ ∘ reduction L N)) frameEnergy :=
    hEnergyTransfer _ (fun W η U J hU hJ hd a b => (hPlane _ hκbar W η).2.2.1 U J hU hJ hd a b)
  have hHam : HammingEstimate (frameSpec (κ ∘ reduction L N)) M ((M : ℝ)/1000) :=
    hHamming _ hReg l p Mstar frameEnergy hα hα1 hFE (hWindow l p Mstar hW _ hκbar) n hn
  have hGauges : ∀ a, Nonempty (BoxGauge L N M a κ) := by
    intro a
    obtain ⟨C⟩ := hCoordinates hAnti L N M hM hL hN (hInject L N M hM hL hN) κ a
    exact ⟨{
      centre := C.centre
      centre_reduces := C.centre_reduces
      change := C.change
      boundary := C.boundary
      carries := hGauge hPositive L N M hM hL hN κ hκ a C
        (hBonds L N M hM hL hN C.centre (hInject L N M hM hL hN C.centre))
      boundary_change := C.boundary_change }⟩
  have hBlocks : UniformBlockGap (torusLaw L N κ) M (blockGapConstant M) := by
    intro a σ
    obtain ⟨G⟩ := hGauges a
    have hPlaneGap : PoincareLower
        ((frameSpec (κ ∘ reduction L N)).law (square G.centre M) (G.boundary σ)) (blockGapConstant M) := by
      simpa only [frameSpec, blockGapConstant, hEdges G.centre M] using
        (hPlane _ hκbar (square G.centre M) (fun z => G.boundary σ z)).2.2.2
    exact hTransportGap _ _ (fun _ => IcoLetter) (fun _ => IcoLetter) G.change _ _
      (G.carries σ) _ hPlaneGap
  have hInfluence : BlockInfluence (torusLaw L N κ) M ((M : ℝ)/1000) := by
    intro a y hy σ τ hστ
    obtain ⟨G⟩ := hGauges a
    obtain ⟨z, hz, _, hBoundary⟩ := G.boundary_change y hy σ τ hστ
    obtain ⟨c, hc⟩ := hHam G.centre z hz (G.boundary σ) (G.boundary τ) hBoundary
    obtain ⟨d, hd⟩ := hTransportCost _ _ (fun _ => IcoLetter) (fun _ => IcoLetter)
      G.change _ _ _ _ (G.carries σ) (G.carries τ) c
    exact ⟨d, hd.trans_le hc⟩
  have hμ := (hTorus L N κ hκ).1
  have hB := hBudget M hM
  have hStrict : (haloCount M : ℝ)*((M : ℝ)/1000) < (volumeCount M : ℝ) := by linarith [hB.2.1]
  have hClassical := (hPeriodic L N (fun _ => IcoLetter) (torusLaw L N κ) hμ M
    (blockGapConstant M) ((M : ℝ)/1000) hM hL hN hg (by positivity)
    (hRange L N κ (hTorus L N κ hκ).2.1 M hM) hBlocks hInfluence hStrict).2
  have hFinalGap : PoincareLower (torusLaw L N κ) ((499/500)*blockGapConstant M) := by
    apply poincareMonotone _ (fun _ => IcoLetter) _ (positiveToProbability _ _ hμ) _ _ _ hClassical
    exact (by nlinarith [mul_le_mul_of_nonneg_left hB.2.2 hg.le])
  have hCoercive := (hQD L N κ hκ).2 _ hFinalGap
  have hKer := (hKernel L N).2.2.2.2.1
  refine ⟨hKer, ?_⟩
  intro μ hμ0 hEigen
  have hBKer : B L N ∈ LinearMap.ker (H L N) := by
    rw [hKer]
    exact Submodule.subset_span (by simp)
  exact rayleighBound L N _ hCoercive μ (groundOrthogonality L N hBKer μ hμ0) hEigen

#print axioms mainW_of_core

/-- Complete assembly from writer-sized closed leaves and the paper's independent
Top inputs. No hypothesis here is a local free-standing assertion about one torus. -/
theorem mainW_of_parts (hFinite : FiniteAssemblyLeaves) (hShell : ShellAssemblyLeaves)
    (hLocal : PeriodicAssemblyLeaves) (hGeometry : ShellGeometryStatement)
    (hFrames : ThreeFramesStatement) (hStar : StarStatement) (hEnergy : PlaneEnergyStatement)
    (hQD : QDStatement) (hKernel : TorusKernelStatement) : MainWStatement := by
  rcases hFinite with ⟨hForm, hLip, hEigen, hSpectralGap, hCond, hMult⟩
  rcases hShell with ⟨hRows, hTrace, hCount, hAbsorb, hFailure, hEndpoint, hSpacing,
    hScale, hTail, hCard, hBudget, hConvert, hFar, hChoose⟩
  rcases hLocal with ⟨hInside, hOutside, hVolume, hNeighbour, hRegular, hFE, hWindow,
    hColour, hPullback, hInject, hBonds, hCoordinates, hGauge, hRange, hEdges, hTGap, hTCost⟩
  have hSpectral := reversibleSpectral_of_parts hEigen hSpectralGap
  have hContract := finiteContraction_of_parts hForm hLip hSpectral
  have hCompare := blockComparison_of_parts hCond hMult
  have hPeriodic := periodicCriterion_of_parts hInside hOutside hVolume hNeighbour hContract hCompare
  have hStopped := stoppedCoupling_of_parts hRows hTrace hCount hAbsorb hFailure hEndpoint hSpacing hGeometry
  have hHamming := hammingAtScale_of_parts hStopped hScale hTail hCard hBudget hConvert hFar
  exact mainW_of_core hChoose hHamming hRegular hFE hWindow hColour hPullback hInject hBonds
    hCoordinates hGauge hRange hEdges hTGap hTCost hPeriodic periodicBudget hFrames hStar hEnergy hQD hKernel

#print axioms reversibleSpectral_of_parts
#print axioms mainW_of_parts

end AKLT.Blueprint.Gap
