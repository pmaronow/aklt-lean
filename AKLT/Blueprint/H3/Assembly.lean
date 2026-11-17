module
public import AKLT.Blueprint.H3.Nodes
public import AKLT.Blueprint.H3.NodesAutomaton
public import AKLT.Blueprint.H3.NodesPhase
public import AKLT.Blueprint.H3.NodesDomination
public import AKLT.Blueprint.H3.NodesCertificate
public import AKLT.Blueprint.H3.NodesPrefix
public import AKLT.Blueprint.H3.NodesReflection
public import AKLT.Blueprint.H3.NodesKernel
public import AKLT.Blueprint.H3.Bellman

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-! Proved implication graph for the H3 blueprint. Every node argument is a closed Prop.
Finite arrays and the 3741-state reconstruction are external checks, never axioms. -/
noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs
namespace AKLT.Blueprint.H3
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 2048

/-- `l:automaton-quotient`: representative construction, closure, and exact rational iterates. -/
theorem automatonQuotient_of_nodes (hRaw : RawSuccessorStatement)
    (hProjection : ProjectionRealizationStatement) : Top.AutomatonQuotientStatement := by
  refine ⟨hProjection, ?_⟩
  intro m q hm Q hQ
  refine ⟨fun w hw d hd => hRaw m hm w hw d hd, ?_⟩
  intro p weight hweight terminal G R
  induction R with
  | zero => intro φ w hw x; rfl
  | succ R ih =>
    intro φ w hw x
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    calc
      rawBackward m p weight terminal
          (((rawBackward m p weight terminal)^[R]) (fun ψ ω y => G ψ (Q.project ω) y)) φ w x =
        rawBackward m p weight terminal
          (fun ψ ω y => ((quotientBackward Q p weight terminal)^[R]) G ψ (Q.project ω) y) φ w x := by
            apply rawBackward_congr
            intro ψ d hd
            exact ih ψ _ (hRaw m hm w hw d hd) _
      _ = _ := rawBackward_pullback Q hQ p weight hweight terminal _ w hw φ x

/-- `l:phase-expansion`: the two terminal-history sums and exact prefix/suffix split. -/
theorem phaseExpansion_of_nodes (hFold : PhaseFoldExpansionStatement)
    (hFactor : SingleChangeFactorStatement) (hExposure : LongExposureExpansionStatement)
    (hCausal : PrefixCoefficientCausalityStatement) (hSplit : PhaseSplitAlgebraStatement) :
    Top.PhaseExpansionStatement := by
  intro n w _
  constructor
  · calc
      (∑ φ : Phase, prefixPhases w φ * phaseTerminal φ) =
          ∑ j : Fin n, (singleChange (trueKind w) (witnessKappa w) j .A .C +
            singleChange (trueKind w) (witnessKappa w) j .B .D) := by
              change (∑ φ : Phase, phaseRun (fun i => phaseTransition (trueKind w i) (witnessKappa w i))
                (List.finRange n) phaseInitial φ * phaseTerminal φ) = _
              exact hFold n (trueKind w) (witnessKappa w)
      _ = ∑ j : Fin n, trailBaseWeight kernelStart w * longRewardTerm w j := by
        exact Finset.sum_congr rfl fun j _ => hFactor n w j
      _ = trailBaseWeight kernelStart w * exposureSum w (witnessKappa w) (longOrdering w) := by
        rw [← Finset.mul_sum, ← hExposure n w]
  · intro L hL
    dsimp only
    have ht : takeWord w L = (fun i : Fin L => w ⟨i.val, Nat.lt_of_lt_of_le i.isLt hL⟩) := by
      funext i
      simp [takeWord, Nat.lt_of_lt_of_le i.isLt hL]
    simpa only [ht] using hSplit n w L hL (hCausal n w L hL)

/-- `l:stationary-domination`: all geometric, local scalar, and path-sum steps are explicit. -/
theorem stationaryDomination_of_nodes
    (hValid : SuffixWindowValidityStatement) (hLabels : SuffixWindowLabelsStatement)
    (hIncident : IncidentBondBudgetStatement) (hBalance : DepartureBalanceStatement)
    (hKnown : KnownSiteMemoryStatement) (hReward : TrueRewardIdentityStatement)
    (hForget : RewardForgettingStatement) (hLocal : LocalCoefficientComparisonStatement)
    (hGeometry : ClosedTrailStepGeometryStatement) (hWord : SuffixWordComparisonStatement)
    (hExpansion : StationaryWordExpansionStatement) : Top.StationaryDominationStatement := by
  have hBudget : ∀ n : ℕ, ∀ w : DirectionWord n, IsTrail kernelStart kernelIncoming w →
      ∀ z : Plane, departureCount kernelStart w n z ≤ 2 := by
    intro n w hw z
    have hi := hIncident n w hw z
    have hb := hBalance n w z
    omega
  have hStep : ∀ Q : MemoryQuotient 10 3741, Q.Correct → ∀ X : PairType,
      ∀ d₀ : Compass, d₀ ≠ .east → ∀ n L : ℕ, 12 ≤ L → L ≤ n → ∀ w : DirectionWord n,
      ClosedTrail X w → SurvivingPrefix X d₀ (takeWord w L) →
      ∀ i : Fin n, L ≤ i.val → ∀ φ ψ : Phase,
        truePhaseCoefficient w i φ ψ ≤ stationaryCoefficient Q X d₀ φ
          (Q.project (suffixWindow w i.val)) (wordVertex kernelStart w i.val) (w i) ψ := by
    intro Q hQ X d₀ hd n L hL hLn w hw hP i hi
    obtain ⟨hraw, had⟩ := hValid n w hw.1 i (by omega)
    obtain ⟨_, harr, hrev, hfirst⟩ := hLabels n w hw.1 i (by omega)
    obtain ⟨hnext, hc, hv, hnc⟩ := hGeometry X n w hw i
    obtain ⟨hnoReverse, hreward⟩ := hReward n w hw.1 i
    have hrewardLe : witnessKappa w i ≤ relaxedReward (wordVertex kernelStart w i.val)
        (wordIncoming kernelIncoming w i) (w i) {kernelCentre} := by
      rw [hreward]
      exact hForget _ _ _ hnoReverse _ _ (by simp [trueDeadSet])
    have hfacts : TrueStepFacts X d₀ w i :=
      ⟨hraw, had, harr, hrev, hfirst, hrewardLe, hc, hv, by simpa only [hnext] using hnc,
        hKnown X d₀ hd n L hL hLn w hw hP (hBudget n w hw.1) i hi⟩
    exact hLocal Q hQ X d₀ n w i hfacts
  refine ⟨hStep, ?_⟩
  intro Q hQ X d₀ hd L hL P hP φ R
  unfold trueContinuationSum stationaryContinuationSum
  apply Finset.sum_le_sum
  intro r _
  rw [hExpansion Q X d₀ r]
  apply Finset.sum_le_sum
  intro v _
  split_ifs with hv
  · apply hWord Q hQ X d₀ L hL P r v hv
    · intro i hi
      apply hStep Q hQ X d₀ hd (L + r) L hL (by omega) _ hv
      simpa only [takeWord_append] using hP
      exact hi
    · intro i hi
      obtain ⟨hraw, had⟩ := hValid (L + r) _ hv.1 i (by omega)
      have hs := ((hQ.2 _ hraw _).2 had).2.1
      exact hs.trans (congrArg Q.project (hLabels (L + r) _ hv.1 i (by omega)).1)
  · exact stationaryWordValue_nonneg Q X d₀ _ _ _ _

/-- `l:Bellman-soundness`: no open mathematical leaves remain in this interface. -/
theorem bellmanSoundness : Top.BellmanSoundnessStatement := bellmanSoundness_proved

/-- `l:stationary-local-global`: free/inside integer rows and caps extend to all lattice sites. -/
theorem stationaryLocalGlobal_of_nodes (hFree : StationaryFreeEdgeStatement) :
    Top.StationaryLocalGlobalStatement := by
  refine ⟨coefficientCeiling_proved, ?_⟩
  intro Q hQ X d₀ hd C hC
  have hrow : ∀ φ a x, stationaryReward X φ a x + stationaryApply Q X d₀ C.potential φ a x ≤
      C.potential φ a x := by
    intro φ a x
    by_cases hc : x = kernelCentre
    · subst x
      have hct : kernelCentre ≠ kernelTarget X := by cases X <;> decide
      simp [stationaryReward, stationaryApply, stationaryCoefficient, hct,
        StationaryData.potential, (hC.2.2.2.2.1 φ a).1]
    by_cases hv : x = kernelTarget X
    · subst x
      have ht := (hC.2.2.2.2.1 φ a).2
      have hV : (certificateValueScale : ℚ) ≠ 0 := by norm_num [certificateValueScale]
      simp [stationaryReward, stationaryApply, stationaryCoefficient, StationaryData.potential,
        ht, hV]
    rw [stationaryReward, ite_eq_right hv, zero_add]
    by_cases hx : x ∈ square (0, 0) certificateRadius
    · exact checked_inside_row Q X d₀ C hC φ a ⟨x, hx⟩ hc hv
    · rw [(potential_bounds C Q X d₀ hC φ a x).2.2 hx]
      calc
        stationaryApply Q X d₀ C.potential φ a x ≤
            freeApply Q (fun ψ b => (C.cap ψ b : ℚ) / certificateValueScale) φ a := by
          apply Finset.sum_le_sum
          intro d _
          apply Finset.sum_le_sum
          intro ψ _
          exact mul_le_mul (hFree Q hQ X d₀ hd φ a x d ψ)
            (potential_bounds C Q X d₀ hC ψ _ _).2.1
            (potential_bounds C Q X d₀ hC ψ _ _).1 (freeCoefficient_nonneg _ _ _ _ _)
        _ ≤ _ := checked_free_row Q X d₀ C hC φ a
  refine ⟨checked_free_row Q X d₀ C hC, ?_⟩
  intro φ a x
  obtain ⟨hn, hb, ho⟩ := potential_bounds C Q X d₀ hC φ a x
  exact ⟨hn, hb, ho, hrow φ a x,
    fun R => stationary_finite_le Q X d₀ C.potential
      (fun ψ b y => (potential_bounds C Q X d₀ hC ψ b y).1) hrow φ a x R⟩

/-- `l:prefix-domination`: exact short ordering, surviving prefixes, and dominated suffixes. -/
theorem prefixDomination_of_nodes (hPhase : Top.PhaseExpansionStatement)
    (hDomination : Top.StationaryDominationStatement) (hGlobal : Top.StationaryLocalGlobalStatement)
    (hPrefix : LongTrailPrefixStatement) (hRegroup : LongRowRegroupingStatement) :
    Top.PrefixDominationStatement := by
  intro Q hQ X d₀ hd C hC R
  have hpot : ∀ φ a x, 0 ≤ C.potential φ a x :=
    fun φ a x => (hGlobal.2 Q hQ X d₀ hd C hC).2 φ a x |>.1
  by_cases hR : R ≤ 12
  · unfold stationaryPrefixBound
    apply (firstDirectionPartialRow_mono X d₀ hR).trans
    apply le_add_of_nonneg_right
    apply Finset.sum_nonneg
    intro P _
    split_ifs
    · exact Finset.sum_nonneg fun φ _ => mul_nonneg (prefixPhases_nonneg P φ) (hpot _ _ _)
    · exact le_rfl
  · have hsplit : ∀ n : ℕ, 12 < n → n ≤ R → ∀ w : DirectionWord n,
        ClosedTrail X w → FirstDirection w d₀ →
        closedContribution w = ∑ φ, prefixPhases (takeWord w 12) φ * truePhaseSuffix w 12 φ := by
      intro n hn _ w hw _
      have he := (hPhase n w hw.1).1
      have hs := (hPhase n w hw.1).2 12 (by omega)
      have ho : kernelOrdering w = longOrdering w := by
        simp only [kernelOrdering, longOrdering, Nat.not_le.mpr hn, ↓reduceIte]
      have hp : closedContribution w = ∑ φ, prefixPhases w φ * phaseTerminal φ := by
        rw [closedContribution, ho, ← he]
      have ht : takeWord w 12 = (fun i : Fin 12 => w ⟨i.val, by omega⟩) := by
        funext i
        simp [takeWord, show i.val < n by omega]
      exact hp.trans (by simpa only [ht] using hs)
    rw [hRegroup X d₀ R (by omega) (wordSplit_proved 12) (hPrefix X d₀) hsplit]
    unfold stationaryPrefixBound
    apply add_le_add le_rfl
    apply Finset.sum_le_sum
    intro P _
    split_ifs with hP
    · apply Finset.sum_le_sum
      intro φ _
      apply mul_le_mul_of_nonneg_left _ (prefixPhases_nonneg P φ)
      exact (hDomination.2 Q hQ X d₀ hd 12 le_rfl P hP φ (R - 12)).trans
        (((hGlobal.2 Q hQ X d₀ hd C hC).2 φ _ _).2.2.2.2 (R - 12))
    · exact le_rfl

/-- Reflection on finite pairs is injective, including on empty and singleton sets. -/
theorem reflectPair_injective : Function.Injective (fun p : Finset Plane => p.image reflectSite) := by
  have hinv : ∀ p : Finset Plane, (p.image reflectSite).image reflectSite = p := by
    intro p
    simp [Finset.image_image, Function.comp_def]
  exact Function.LeftInverse.injective hinv

/-- `l:kernel-reflection`: pair transport gives rewards; finite-list congruence gives order;
the involution then transports every finite first-direction sum. -/
theorem kernelReflection_of_nodes (hGeometry : ReflectionGeometryStatement)
    (hPairs : ReflectionPairsStatement) : Top.KernelReflectionStatement := by
  have hReward : ∀ n : ℕ, ∀ w : DirectionWord n, ∀ i : Fin n,
      witnessKappa w i = witnessKappa (reflectWord w) i := by
    intro n w i
    unfold witnessKappa
    rw [← (hPairs n w i).1, Finset.sum_image (fun _ _ _ _ h => reflectPair_injective h)]
    apply Finset.sum_congr rfl
    intro p hp
    obtain ⟨hc, ht, _⟩ := (hPairs n w i).2 p hp
    rw [← hc, ← ht]
  have hAll : ∀ n : ℕ, ∀ w : DirectionWord n,
      (ClosedTrail .B w ↔ ClosedTrail .B (reflectWord w)) ∧
      (FirstDirection w .north ↔ FirstDirection (reflectWord w) .south) ∧
      trailWeight kernelStart kernelIncoming w = trailWeight kernelStart kernelIncoming (reflectWord w) ∧
      kernelOrdering w = kernelOrdering (reflectWord w) ∧
      closedContribution w = closedContribution (reflectWord w) ∧
      ∀ i : Fin n, wordStraight kernelIncoming w i = wordStraight kernelIncoming (reflectWord w) i ∧
        wordRevisit kernelStart w i = wordRevisit kernelStart (reflectWord w) i ∧
        (responsePairs w i).image (fun p => p.image reflectSite) = responsePairs (reflectWord w) i ∧
        ∀ p ∈ responsePairs w i,
          pairCoefficient w i p = pairCoefficient (reflectWord w) i (p.image reflectSite) ∧
          responsePairType p = responsePairType (p.image reflectSite) ∧
          pairShift .B p = pairShift .B (p.image reflectSite) := by
    intro n w
    obtain ⟨_, hc, hf, hi⟩ := hGeometry n w
    obtain ⟨hw, ho, hcon⟩ := reflectionOrderingAlgebra_proved n w
      (fun i => ⟨(hi i).1, (hi i).2, hReward n w i⟩)
    exact ⟨hc, hf, hw, ho, hcon, fun i => ⟨(hi i).1, (hi i).2, (hPairs n w i).1, (hPairs n w i).2⟩⟩
  refine ⟨hAll, ?_⟩
  intro R
  unfold firstDirectionPartialRow
  apply Finset.sum_congr rfl
  intro n _
  apply Fintype.sum_equiv (reflectWordEquiv n)
  intro w
  obtain ⟨hc, hf, _, _, hcon, _⟩ := hAll n w
  change (if ClosedTrail .B w ∧ FirstDirection w .north then closedContribution w else 0) =
    (if ClosedTrail .B (reflectWord w) ∧ FirstDirection (reflectWord w) .south then
      closedContribution (reflectWord w) else 0)
  rw [hc, hf, hcon]

/-- `l:stationary-assembly`, lines 1198–1225: the exact denominator-cleared ceilings
imply both final row bounds. All constants are rational; the adopted dyadic witness is retained. -/
theorem ceiling_rows (bN bW cN cW cS : ℚ)
    (hbN : (10^9 : ℚ) * bN ≤ stationaryPrefixCeiling .B .north)
    (hbW : (10^9 : ℚ) * bW ≤ stationaryPrefixCeiling .B .west)
    (hcN : (10^9 : ℚ) * cN ≤ stationaryPrefixCeiling .C .north)
    (hcW : (10^9 : ℚ) * cW ≤ stationaryPrefixCeiling .C .west)
    (hcS : (10^9 : ℚ) * cS ≤ stationaryPrefixCeiling .C .south) :
    (2 * bN + bW ≤ kernelRho * kernelWitness .B) ∧
      (cN + cW + cS ≤ kernelRho * kernelWitness .C) := by
  norm_num [stationaryPrefixCeiling] at hbN hbW hcN hcW hcS
  constructor
  · norm_num [kernelRho, kernelWitness]
    linarith
  · norm_num [kernelRho, kernelWitness]
    linarith

/-- `l:stationary-assembly`: five cases imply all finite and infinite row bounds. -/
theorem stationaryAssembly_of_nodes (hPrefix : Top.PrefixDominationStatement)
    (hReflection : Top.KernelReflectionStatement) (hPartition : FirstDirectionPartitionStatement)
    (hSupport : LengthShiftSupportStatement) (hLength : LengthRewardPartitionStatement)
    (hSeries : KernelSeriesRegroupingStatement) (hLift : CutoffSeriesLiftStatement) :
    Top.StationaryAssemblyStatement := by
  intro Q hQ C hC
  have hcase : ∀ k ∈ stationaryCases, ∀ R : ℕ,
      firstDirectionPartialRow k.1 k.2 R ≤ stationaryPrefixBound Q k.1 k.2 (C k) := by
    intro k hk R
    have hd : k.2 ≠ .east := by
      simp only [stationaryCases, Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide
    exact hPrefix Q hQ k.1 k.2 hd (C k) (hC k hk).1 R
  have hBN : (.B, .north) ∈ stationaryCases := by simp [stationaryCases]
  have hBW : (.B, .west) ∈ stationaryCases := by simp [stationaryCases]
  have hCN : (.C, .north) ∈ stationaryCases := by simp [stationaryCases]
  have hCW : (.C, .west) ∈ stationaryCases := by simp [stationaryCases]
  have hCS : (.C, .south) ∈ stationaryCases := by simp [stationaryCases]
  have hB : ∀ R : ℕ, kernelPartialRow .B R ≤
      2 * stationaryPrefixBound Q .B .north (C (.B, .north)) +
        stationaryPrefixBound Q .B .west (C (.B, .west)) := by
    intro R
    rw [hPartition, ← hReflection.2 R]
    linarith [hcase (.B, .north) hBN R, hcase (.B, .west) hBW R]
  have hCrow : ∀ R : ℕ, kernelPartialRow .C R ≤
      stationaryPrefixBound Q .C .north (C (.C, .north)) +
        stationaryPrefixBound Q .C .west (C (.C, .west)) +
        stationaryPrefixBound Q .C .south (C (.C, .south)) := by
    intro R
    rw [hPartition]
    linarith [hcase (.C, .north) hCN R, hcase (.C, .west) hCW R, hcase (.C, .south) hCS R]
  obtain ⟨hBc, hCc⟩ := ceiling_rows _ _ _ _ _ (hC _ hBN).2 (hC _ hBW).2
    (hC _ hCN).2 (hC _ hCW).2 (hC _ hCS).2
  have hH3 : Top.H3Statement := by
    intro X R
    cases X
    · exact (hB R).trans hBc
    · exact (hCrow R).trans hCc
  have hFull : ∀ X : PairType,
      (∑ Y : PairType, shiftedKernel 1 X Y * ENNReal.ofReal (kernelWitness Y : ℝ)) ≤
        ENNReal.ofReal ((kernelRho * kernelWitness X : ℚ) : ℝ) := by
    intro X
    rw [hSeries X (fun Y n s hs => hSupport X Y n s hs) (hLength X)]
    exact hLift (kernelLengthRow X) (kernelLengthRow_nonneg X) (kernelLengthRow_zero X)
      (kernelRho * kernelWitness X) (hH3 X)
  exact ⟨hB, hBc, hCrow, hCc, hFull, hH3⟩

/-- `h:H3` from the two external data checks and the analytic stationary assembly.
StationaryCheck already contains its own Correct quotient. Automaton10 is retained as an
explicit provenance input; its counts are not needed again for this logical implication. -/
theorem h3_of_checks (_hAutomaton : Top.Automaton10Statement)
    (hCheck : Top.StationaryCheckStatement) (hAssembly : Top.StationaryAssemblyStatement) :
    Top.H3Statement := by
  obtain ⟨_, Q, hQ, C, hC⟩ := hCheck
  exact (hAssembly Q hQ C hC).2.2.2.2.2

/-- Complete target package. Only the thirty analytic leaves and the two external finite
checks are hypotheses. In particular no local/global, prefix or reflection Top result remains
an assumed input to this theorem. -/
theorem allTargets_of_leaves_and_checks (h : AnalyticLeavesStatement)
    (hAutomaton : Top.Automaton10Statement) (hCheck : Top.StationaryCheckStatement) :
    Top.AutomatonQuotientStatement ∧ Top.PhaseExpansionStatement ∧
    Top.StationaryDominationStatement ∧ Top.BellmanSoundnessStatement ∧
    Top.StationaryLocalGlobalStatement ∧ Top.PrefixDominationStatement ∧
    Top.KernelReflectionStatement ∧ Top.StationaryAssemblyStatement ∧ Top.H3Statement := by
  obtain ⟨hRaw, hProjection, hFold, hFactor, hExposureList, hLongOrder, hCausal, hSplit,
    hValid, hLabels, hIncident, hBalance, hKnown, hReward, hForget, hLocal, hGeometry,
    hWord, hExpansion, hFree, hPrefix, hRegroup, hReflectGeometry, hReflectLive, hReflectLabels,
    hPartition, hSupport, hLength, hSeries, hLift⟩ := h
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
  exact ⟨automatonQuotient_of_nodes hRaw hProjection, hPhase, hDom, bellmanSoundness,
    hGlobal, hPrefixTop, hReflection, hAssembly, h3_of_checks hAutomaton hCheck hAssembly⟩

#print axioms automatonQuotient_of_nodes
#print axioms phaseExpansion_of_nodes
#print axioms stationaryDomination_of_nodes
#print axioms bellmanSoundness
#print axioms stationaryLocalGlobal_of_nodes
#print axioms prefixDomination_of_nodes
#print axioms kernelReflection_of_nodes
#print axioms stationaryAssembly_of_nodes
#print axioms h3_of_checks
#print axioms allTargets_of_leaves_and_checks
#print axioms reflectPair_injective
#print axioms ceiling_rows

end AKLT.Blueprint.H3
