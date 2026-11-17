module
public import AKLT.Blueprint.Rec.NodesV2Handoff
public import AKLT.Blueprint.Top.Assembly

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-! Adapted assemblies only. New mathematical leaf proofs are intentionally
absent: unchanged statements come from the frozen nodes and changed statements
come from NodesV2*. The shared matcher is not the frozen Rec-local V2. -/

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs

namespace AKLT.Blueprint.Rec

/-- The sole changed input of the typed numeric assembly is the full-scope
integrated lower bound. All moment intervals and analytic comparisons are frozen. -/
structure TypedLeavesV2 : Prop where
  lower : CoveredIntegratedLowerStatementV2
  threeIntervals : RemovedMeanIntervalsStatement
  twoIntervals : TwoMeanIntervalsStatement
  betaPrime : BetaPrimeAnalyticStatement
  beta : BetaAnalyticStatement
  alpha : AlphaAnalyticStatement

/-- Retarget l:response without changing any leaf or its original Top contract. -/
theorem response_of_leavesV2 (h : ResponseLeaves) : Top.ResponseStatement :=
  response_of_leaves h

/-- The logarithmic-mean contract and its exact rational leaf proofs are unchanged. -/
theorem logMeanBounds_of_leavesV2 (hx : LogCoefficientMonoXStatement)
    (hy : LogCoefficientMonoYStatement) (hl : LogEnclosureLowerStatement)
    (hu : LogEnclosureUpperStatement) : Top.LogMeanBoundsStatement :=
  logMeanBounds_of_leaves hx hy hl hu

/-- l:response-typed at ARCH_0's shared internal-present-bond matcher. This
assembles the same analytic/rational inequalities at the broadened departure class. -/
theorem responseTyped_shared_of_leavesV2 (hR : Top.ResponseStatement)
    (hL : Top.LogMeanBoundsStatement) (h : TypedLeavesV2) : Top.ResponseTypedStatementV2 := by
  classical
  rcases hL with ⟨_, _, _, henc, hrows⟩
  intro hH1
  refine ⟨typedCrudeRows, ?_⟩
  intro G τ D hD y hy hU incoming outgoing hcov
  let o := y + outgoing.step
  let straight := decide (outgoing = incoming)
  have hc : (3 / 5 : ℝ) ≤ localThreshold straight ∧ (localThreshold straight : ℝ) ≤ 1 := by
    cases hs : straight <;> norm_num [localThreshold]
  have hcq : (0 : ℚ) < localThreshold straight ∧ localThreshold straight < 1 := by
    cases hs : straight <;> norm_num [localThreshold]
  have hca : (0 : ℚ) < (116 / 125) * localThreshold straight ∧
      (116 / 125 : ℚ) * localThreshold straight < 1 := by
    cases hs : straight <;> norm_num [localThreshold]
  have eup : reciprocalLogMean (localThreshold straight : ℝ) ≤
      (logMeanUpper (localThreshold straight) : ℝ) := (henc _ hcq.1 hcq.2).2
  have eaup : reciprocalLogMean ((116 / 125) * (localThreshold straight : ℝ)) ≤
      (logMeanUpper ((116 / 125) * localThreshold straight) : ℝ) := by
    simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (henc _ hca.1 hca.2).2
  have ealow : (logMeanLower (116 / 125) : ℝ) ≤ reciprocalLogMean (116 / 125) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using
      (henc (116 / 125) (by norm_num) (by norm_num)).1
  have row := hrows straight
  have rowα : (logMeanUpper ((116 / 125) * localThreshold straight) : ℝ) / 3 -
      (logMeanLower (116 / 125) : ℝ) / 5 ≤ (alphaBound straight : ℝ) := by exact_mod_cast row.1
  have rowβ : (logMeanUpper ((116 / 125) * localThreshold straight) : ℝ) / 3 ≤
      (betaBound straight : ℝ) := by exact_mod_cast row.2.1
  have rowβ' : (logMeanUpper (localThreshold straight) : ℝ) / 3 ≤
      (betaPrimeBound straight : ℝ) := by exact_mod_cast row.2.2.1
  constructor
  · intro f hs hne
    have ho : o ∈ D.presentNeighbors y := by rw [hs]; simp [o]
    let a : Departure := ⟨G, τ, D, y, o, hD, hy, ho⟩
    rcases hR G τ D hD y hy o ho with ⟨_, _, _, _, _, _, htwo, _⟩
    have low := (h.lower hH1 a hU incoming outgoing rfl hcov).1 f hs hne
    have free := (h.twoIntervals a hU f hs hne).2
    have ana : responseBetaPrime D τ y o f ≤ reciprocalLogMean (localThreshold straight : ℝ) / 3 :=
      h.betaPrime _ _ _ (by linarith [hc.1]) low free
    exact ⟨(htwo f hU hs hne).1, by linarith, ana⟩
  · intro f g hs hof hog hfg
    have ho : o ∈ D.presentNeighbors y := by rw [hs]; simp [o]
    let a : Departure := ⟨G, τ, D, y, o, hD, hy, ho⟩
    rcases hR G τ D hD y hy o ho with ⟨_, _, _, _, _, _, _, hthree⟩
    have base := hthree f g hU hs hof hog hfg
    have low := (h.lower hH1 a hU incoming outgoing rfl hcov).2 f g hs hof hog hfg
    have ints := h.threeIntervals a hU f g hs hof hog hfg
    have anaβ : responseBeta D τ y o f g ≤
        reciprocalLogMean ((116 / 125) * (localThreshold straight : ℝ)) / 3 :=
      h.beta _ _ _ _ _ hc.1 hc.2 low ints.2.2 (ints.1 true).2.2.1 ints.2.1
    have anaα : responseAlpha D τ y o f g ≤
        reciprocalLogMean ((116 / 125) * (localThreshold straight : ℝ)) / 3 -
          reciprocalLogMean (116 / 125) / 5 :=
      h.alpha _ _ _ _ _ hc.1 hc.2 low ints.2.2 (ints.1 true).2.2.1 ints.2.1
    exact ⟨base.1, by linarith, base.2.2.1, by linarith, anaβ, anaα,
      low, ints.2.2, ints.2.1, (ints.1 true).2.2.1⟩


/-- Preserve the legacy Top interface as a specialization, conditional on
the new open comparison obligation. No converse between matchers is assumed. -/
theorem legacyTyped_of_sharedV2 (hT : Top.ResponseTypedStatementV2)
    (hcover : LegacyCoverComparisonStatementV2) : Top.ResponseTypedStatement := by
  intro hH1
  refine ⟨(hT hH1).1, ?_⟩
  intro G τ D hD y hy hU incoming outgoing hcov
  exact (hT hH1).2 G τ D hD y hy hU incoming outgoing
    (hcover G D hD y incoming outgoing (coveredDeparture_to_v2 hD hcov))

/-- The fixed kernel and witness interface is preserved by the repairs. -/
theorem mTheta_of_leavesV2 (h : MThetaLeaves) : Top.MThetaStatement :=
  mTheta_of_leaves h

/-- MainV2_of_partsV2 still needs exactly this RecStatement, with its
original H1/H2/H3 premises and explicit renewal amplitude. -/
theorem rec_of_leavesV2 (hM : Top.MThetaStatement) (hN : BoundedRenewalStatement)
    (h : RecursionLeaves) : Top.RecStatement :=
  rec_of_leaves hM hN h

/-- The paper-scope order contract assembled from the frozen permutation
fact and the two new domain/order obligations. This is not an open leaf. -/
def KernelOrderScopeStatementV2 : Prop :=
  ∀ n : ℕ, ∀ X : PairType, ∀ w : DirectionWord n, ClosedTrail X w →
    (kernelOrdering w).Perm (firstVisitList w) ∧ (kernelOrdering w).Nodup ∧
    (n ≤ 12 → kernelOrdering w = (firstVisitList w).mergeSort (shortOrderLE w) ∧
      (kernelOrdering w).Pairwise (fun i j => shortOrderLE w i j = true)) ∧
    (12 < n → kernelOrdering w = longOrdering w ∧
      ((firstVisitList w).filter (wordStraight kernelIncoming w)).Pairwise
        (fun i j => i.val < j.val) ∧
      ((firstVisitList w).filter (fun i => !wordStraight kernelIncoming w i)).Pairwise
        (fun i j => i.val < j.val))

/-- REF2_5 finding 2 and REF2_6 finding 2: specify both branches on
the actual kernel-trail domain, with exact within-type path order. -/
theorem kernelOrderScope_of_leavesV2 (hp : KernelOrderingStatement)
    (hs : ShortKernelOrderingStatementV2) (hl : LongKernelOrderingStatementV2) :
    KernelOrderScopeStatementV2 := by
  intro n X w hclosed
  exact ⟨(hp n w).1, (hp n w).2, hs n X w hclosed, hl n X w hclosed⟩

/-- Only a LONG kernel trail may replace its prescribed kernel ordering
by the order evaluated by the phase expansion. This is an assembled handoff. -/
def LongPhaseKernelStatementV2 : Prop :=
  ∀ n : ℕ, ∀ X : PairType, ∀ w : DirectionWord n, ClosedTrail X w → 12 < n →
    (∑ φ, prefixPhases w φ * phaseTerminal φ) = closedContribution w

/-- Keep the phase algebra as BP_H3M's explicit closed input; only order
agreement and the length-qualified conversion belong to this Rec assembly. -/
theorem longPhaseKernel_of_partsV2 (hPhase : Top.PhaseExpansionStatementV2)
    (hLong : LongKernelOrderingStatementV2) : LongPhaseKernelStatementV2 := by
  intro n X w hclosed hn
  rw [closedContribution, (hLong n X w hclosed hn).1]
  exact (hPhase n X w hclosed).1

/-- Current Rec target list. Four contracts retain their original names;
the typed coefficient target is the repaired shared Top V2 declaration. -/
def TargetsStatementV2 : Prop :=
  Top.ResponseStatement ∧ Top.LogMeanBoundsStatement ∧ Top.ResponseTypedStatementV2 ∧
    Top.MThetaStatement ∧ Top.RecStatement

/-- Core assembly inputs. Only the typed lower-bound field is versioned;
all other exact estimates have unchanged closed conclusions and are reused. -/
structure AssemblyLeavesV2 : Prop where
  response : ResponseLeaves
  logX : LogCoefficientMonoXStatement
  logY : LogCoefficientMonoYStatement
  logLower : LogEnclosureLowerStatement
  logUpper : LogEnclosureUpperStatement
  typed : TypedLeavesV2
  matrix : MThetaLeaves
  iterate : RenewalFiniteIterationStatement
  remainder : RenewalRemainderStatement
  source : RenewalSourceStatement
  limit : RenewalScalarLimitStatement
  recursion : RecursionLeaves

/-- All repaired Rec targets from frozen leaves plus the broadened local
lower-bound leaf. No numerical data check is discharged by this implication. -/
theorem targets_of_leavesV2 (h : AssemblyLeavesV2) : TargetsStatementV2 := by
  have hR := response_of_leavesV2 h.response
  have hL := logMeanBounds_of_leavesV2 h.logX h.logY h.logLower h.logUpper
  have hT := responseTyped_shared_of_leavesV2 hR hL h.typed
  have hM := mTheta_of_leavesV2 h.matrix
  have hN := boundedRenewal_of_leaves h.iterate h.remainder h.source h.limit
  exact ⟨hR, hL, hT, hM, rec_of_leavesV2 hM hN h.recursion⟩

/-- The strengthened computational package supplies the same semantic
H1/H2/H3 to Rec. Its additional finite-data checks remain explicit inputs. -/
theorem responseProperty_of_inputsV2 (hInputs : Top.InputsStatementV2)
    (hRec : Top.RecStatement) : Top.PStatement := by
  obtain ⟨θ, ρ, _, _, _, _, _, hP⟩ := hRec 10 (certifiedRate : ℝ)
    hInputs.1.1 hInputs.1.2.1 hInputs.1.2.2.1
  exact ⟨Top.renewalAmplitude 10 (certifiedRate : ℝ) ρ, θ, hP⟩

/-- A checked connection to the repaired headline assembly. BP_REC supplies
RecStatement; the archive-bound input package, windows, MainW, and uniqueness
remain closed inputs owned by their respective lanes. -/
theorem mainV2_of_blueprintV2 (hInputs : Top.InputsStatementV2)
    (h : AssemblyLeavesV2) (hCut : Top.CutMOSStatement)
    (hMainW : Top.MainWStatement) (hKernel : Top.TorusKernelStatement) :
    AKLT.Challenge.MainStatementV2 :=
  Top.mainV2_of_partsV2 hInputs (targets_of_leavesV2 h).2.2.2.2 hCut hMainW hKernel

end AKLT.Blueprint.Rec
