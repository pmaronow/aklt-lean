import AKLT.Blueprint.H3.Assembly
import AKLT.Blueprint.H3.NodesV2
import AKLT.Blueprint.Top.Assembly

/-! Adaptation assemblies only. Every new mathematical bridge remains a closed open leaf
in NodesV2*.lean. All thirteen pre-adaptation Lean files are preserved byte-for-byte. -/
noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs

namespace AKLT.Blueprint.H3

/-- The shared quotient Top statement already uses pulled-back terminal data. The extra
paper-facing clause now states both pullback hypotheses for general terminal tests/rewards. -/
theorem automatonQuotient_of_nodesV2 (hRaw : RawSuccessorStatement)
    (hProjection : ProjectionRealizationStatement)
    (hStopped : StoppedQuotientIntertwiningStatementV2) : AutomatonQuotientPaperStatementV2 := by
  refine ⟨automatonQuotient_of_nodes hRaw hProjection, ?_⟩
  intro m q hm Q hQ
  exact hStopped m q hm Q hQ (hRaw m hm)

/-- ARCH_0 F8: restrict the frozen general phase algebra to actual row-X kernel trails. -/
theorem phaseExpansion_of_legacyV2 (hPhase : Top.PhaseExpansionStatement) :
    Top.PhaseExpansionStatementV2 := by
  intro n X w hw
  exact hPhase n w hw.1

/-- REF2_6 finding 2: the actual kernel contribution agrees with the chronological
straight-first phase fold only in the long branch of kernelOrdering. -/
theorem longTrailPhaseExpansion_of_phaseV2 (hPhase : Top.PhaseExpansionStatementV2) :
    LongTrailPhaseExpansionStatementV2 := by
  intro n X w hw hn
  obtain ⟨hFormula, hSplit⟩ := hPhase n X w hw
  refine ⟨?_, hSplit⟩
  simpa only [closedContribution, kernelOrdering, longOrdering, Nat.not_le.mpr hn, ↓reduceIte]
    using hFormula

/-- True closed trails never enter the centre. Thus the new pointwise operator has
identical coefficients along them; its fixed-reward continuation sum is identified by the
separate open continuation bridge. Every premise here is a closed Prop. -/
theorem stationaryDomination_of_legacyV2 (hDomination : Top.StationaryDominationStatement)
    (hGeometry : ClosedTrailStepGeometryStatement)
    (hOffCentre : StationaryCoefficientOffCentreStatementV2)
    (hContinuation : StationaryContinuationBridgeStatementV2) :
    Top.StationaryDominationStatementV2 := by
  constructor
  · intro Q hQ X d₀ hd n L hL hLn w hw hP i hi φ ψ
    obtain ⟨hnext, _, _, hNoCentre⟩ := hGeometry X n w hw i
    have hDestination : wordVertex kernelStart w i.val + (w i).step ≠ kernelCentre := by
      simpa only [hnext] using hNoCentre
    rw [hOffCentre 10 3741 Q X d₀ φ _ _ _ ψ hDestination]
    exact hDomination.1 Q hQ X d₀ hd n L hL hLn w hw hP i hi φ ψ
  · intro Q hQ X d₀ hd L hL P hP φ R
    rw [hContinuation Q X d₀ φ _ _ R]
    exact hDomination.2 Q hQ X d₀ hd L hL P hP φ R

/-- A V2 passing table supplies the legacy row hypotheses through an explicit open bridge.
Its checked centre value is zero, so the second open bridge transfers the Bellman inequality;
the third transfers every finite stopped sum. No equality on arbitrary functions is claimed. -/
theorem stationaryLocalGlobal_of_legacyV2 (hGlobal : Top.StationaryLocalGlobalStatement)
    (hCertificate : StationaryCertificateBridgeStatementV2)
    (hOperator : StationaryCentreZeroOperatorStatementV2)
    (hContinuation : StationaryContinuationBridgeStatementV2) :
    Top.StationaryLocalGlobalStatementV2 := by
  refine ⟨hGlobal.1, ?_⟩
  intro Q hQ X d₀ hd C hC
  have hOld : C.Passes Q X d₀ := hCertificate 10 3741 Q X d₀ C hC
  have hValues := hGlobal.2 Q hQ X d₀ hd C hOld
  have hCentre : ∀ φ a, C.potential φ a kernelCentre = 0 := by
    intro φ a
    change (C.extended φ a kernelCentre : ℚ) / certificateValueScale = 0
    rw [(hOld.2.2.2.2.1 φ a).1]
    simp only [Nat.cast_zero, zero_div]
  refine ⟨hValues.1, ?_⟩
  intro φ a x
  obtain ⟨hNonneg, hCap, hOutside, hRow, hFinite⟩ := hValues.2 φ a x
  refine ⟨hNonneg, hCap, hOutside, ?_, ?_⟩
  · rw [hOperator 10 3741 Q X d₀ C.potential hCentre φ a x]
    exact hRow
  · intro R
    rw [hContinuation Q X d₀ φ a x R]
    exact hFinite R

/-- The exact prefix-bound definition and true finite rows did not change. The passing
certificate bridge permits direct reuse of the frozen prefix assembly and all its multiplicities. -/
theorem prefixDomination_of_legacyV2 (hPrefix : Top.PrefixDominationStatement)
    (hCertificate : StationaryCertificateBridgeStatementV2) : Top.PrefixDominationStatementV2 := by
  intro Q hQ X d₀ hd C hC R
  exact hPrefix Q hQ X d₀ hd C (hCertificate 10 3741 Q X d₀ C hC) R

/-- Five corrected passing cases have the same exact prefix expressions. Transfer the
case hypotheses, then reuse the previously checked finite/full row assembly unchanged. -/
theorem stationaryAssembly_of_legacyV2 (hAssembly : Top.StationaryAssemblyStatement)
    (hCertificate : StationaryCertificateBridgeStatementV2) : Top.StationaryAssemblyStatementV2 := by
  intro Q hQ C hC
  apply hAssembly Q hQ C
  intro k hk
  exact ⟨hCertificate 10 3741 Q k.1 k.2 (C k) (hC k hk).1, (hC k hk).2⟩

/-- Both finite checks now refer to the same designated archive quotient. Use Correct
from the automaton check and the five tables from the stationary check; no class relabeling
or equality between unrelated existential witnesses is assumed. H3 itself is unchanged. -/
theorem h3_of_checksV2 (hAutomaton : Top.Automaton10StatementV2)
    (hCheck : Top.StationaryCheckStatementV2) (hAssembly : Top.StationaryAssemblyStatementV2) :
    Top.H3Statement := by
  obtain ⟨_, C, hC⟩ := hCheck.2
  have hQ : Automaton10Data.supplied.Correct := hAutomaton.2.2.2.2.1
  exact (hAssembly Automaton10Data.supplied hQ C hC).2.2.2.2.2

/-- The complete repaired Top target package follows from the unchanged thirty leaves,
the five new bridges, and the two repaired finite data checks. No new leaf proof is attempted. -/
theorem allTargets_of_leaves_and_checksV2 (h : AnalyticLeavesStatement)
    (hNew : AdaptationLeavesStatementV2) (hAutomaton : Top.Automaton10StatementV2)
    (hCheck : Top.StationaryCheckStatementV2) :
    Top.AutomatonQuotientStatement ∧ Top.PhaseExpansionStatementV2 ∧
    Top.StationaryDominationStatementV2 ∧ Top.BellmanSoundnessStatement ∧
    Top.StationaryLocalGlobalStatementV2 ∧ Top.PrefixDominationStatementV2 ∧
    Top.KernelReflectionStatement ∧ Top.StationaryAssemblyStatementV2 ∧ Top.H3Statement := by
  obtain ⟨hRaw, hProjection, hFold, hFactor, hExposureList, hLongOrder, hCausal, hSplit,
    hValid, hLabels, hIncident, hBalance, hKnown, hReward, hForget, hLocal, hGeometry,
    hWord, hExpansion, hFree, hPrefix, hRegroup, hReflectGeometry, hReflectLive, hReflectLabels,
    hPartition, hSupport, hLength, hSeries, hLift⟩ := h
  obtain ⟨hOffCentre, hOperator, hContinuation, hCertificate, _⟩ := hNew
  have hPhase := phaseExpansion_of_nodes hFold hFactor
    (longExposureExpansion_of_nodes hExposureList hLongOrder) hCausal hSplit
  have hDom := stationaryDomination_of_nodes hValid hLabels hIncident hBalance hKnown
    hReward hForget hLocal hGeometry hWord hExpansion
  have hGlobal := stationaryLocalGlobal_of_nodes hFree
  have hPrefixTop := prefixDomination_of_nodes hPhase hDom hGlobal hPrefix hRegroup
  have hReflection := kernelReflection_of_nodes hReflectGeometry
    (reflectionPairs_of_nodes hReflectLive hReflectLabels)
  have hAssembly := stationaryAssembly_of_nodes hPrefixTop hReflection hPartition hSupport
    hLength hSeries hLift
  have hAssemblyV2 := stationaryAssembly_of_legacyV2 hAssembly hCertificate
  exact ⟨automatonQuotient_of_nodes hRaw hProjection, phaseExpansion_of_legacyV2 hPhase,
    stationaryDomination_of_legacyV2 hDom hGeometry hOffCentre hContinuation, bellmanSoundness,
    stationaryLocalGlobal_of_legacyV2 hGlobal hCertificate hOperator hContinuation,
    prefixDomination_of_legacyV2 hPrefixTop hCertificate, hReflection, hAssemblyV2,
    h3_of_checksV2 hAutomaton hCheck hAssemblyV2⟩

/-- Add the two explicit referee clarifications to the repaired Top package: terminal
indicator/reward pullbacks, and equality with the actual contribution only for long trails. -/
theorem paperTargets_of_leaves_and_checksV2 (h : AnalyticLeavesStatement)
    (hNew : AdaptationLeavesStatementV2) (hAutomaton : Top.Automaton10StatementV2)
    (hCheck : Top.StationaryCheckStatementV2) :
    (Top.AutomatonQuotientStatement ∧ Top.PhaseExpansionStatementV2 ∧
      Top.StationaryDominationStatementV2 ∧ Top.BellmanSoundnessStatement ∧
      Top.StationaryLocalGlobalStatementV2 ∧ Top.PrefixDominationStatementV2 ∧
      Top.KernelReflectionStatement ∧ Top.StationaryAssemblyStatementV2 ∧ Top.H3Statement) ∧
    AutomatonQuotientPaperStatementV2 ∧ LongTrailPhaseExpansionStatementV2 := by
  have hTargets := allTargets_of_leaves_and_checksV2 h hNew hAutomaton hCheck
  exact ⟨hTargets, automatonQuotient_of_nodesV2 h.1 h.2.1 hNew.2.2.2.2,
    longTrailPhaseExpansion_of_phaseV2 hTargets.2.1⟩

/-- Closed H3 handoff for the semantic input package. -/
theorem h3_of_leaves_and_checksV2 (h : AnalyticLeavesStatement)
    (hNew : AdaptationLeavesStatementV2) (hAutomaton : Top.Automaton10StatementV2)
    (hCheck : Top.StationaryCheckStatementV2) : Top.H3Statement :=
  (allTargets_of_leaves_and_checksV2 h hNew hAutomaton hCheck).2.2.2.2.2.2.2.2

/-- Supply precisely the H3 contribution to InputsStatementV2. H1, H2, its two rate
comparisons and H1 finite-data coverage remain explicit other-lane inputs. -/
theorem inputs_of_leaves_and_other_partsV2 (h : AnalyticLeavesStatement)
    (hNew : AdaptationLeavesStatementV2) (hAutomaton : Top.Automaton10StatementV2)
    (hCheck : Top.StationaryCheckStatementV2) (hH1 : Top.H1Statement) (hH2 : Top.H2Statement)
    (hRates : certifiedRate < (2499 / 2500 : ℚ) ∧ (2499 / 2500 : ℚ) < 1)
    (hH1Data : Top.H1FiniteDataStatementV2) : Top.InputsStatementV2 := by
  exact ⟨⟨hH1, hH2, h3_of_leaves_and_checksV2 h hNew hAutomaton hCheck, hRates.1, hRates.2⟩,
    hH1Data, hAutomaton, hCheck⟩

/-- Optional complete headline assembly through the repaired mainV2_of_partsV2. This
proves only the implication; all foreign-lane and numerical coverage inputs stay explicit. -/
theorem mainV2_of_H3_and_other_partsV2 (h : AnalyticLeavesStatement)
    (hNew : AdaptationLeavesStatementV2) (hAutomaton : Top.Automaton10StatementV2)
    (hCheck : Top.StationaryCheckStatementV2) (hH1 : Top.H1Statement) (hH2 : Top.H2Statement)
    (hRates : certifiedRate < (2499 / 2500 : ℚ) ∧ (2499 / 2500 : ℚ) < 1)
    (hH1Data : Top.H1FiniteDataStatementV2) (hRec : Top.RecStatement)
    (hCut : Top.CutMOSStatement) (hMainW : Top.MainWStatement) (hKernel : Top.TorusKernelStatement) :
    AKLT.Challenge.MainStatementV2 := by
  exact Top.mainV2_of_partsV2
    (inputs_of_leaves_and_other_partsV2 h hNew hAutomaton hCheck hH1 hH2 hRates hH1Data)
    hRec hCut hMainW hKernel

#print axioms automatonQuotient_of_nodesV2
#print axioms phaseExpansion_of_legacyV2
#print axioms longTrailPhaseExpansion_of_phaseV2
#print axioms stationaryDomination_of_legacyV2
#print axioms stationaryLocalGlobal_of_legacyV2
#print axioms prefixDomination_of_legacyV2
#print axioms stationaryAssembly_of_legacyV2
#print axioms h3_of_checksV2
#print axioms allTargets_of_leaves_and_checksV2
#print axioms paperTargets_of_leaves_and_checksV2
#print axioms h3_of_leaves_and_checksV2
#print axioms inputs_of_leaves_and_other_partsV2
#print axioms mainV2_of_H3_and_other_partsV2

end AKLT.Blueprint.H3
