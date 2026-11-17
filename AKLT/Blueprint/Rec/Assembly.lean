module
public import AKLT.Blueprint.Rec.NodesRenewal

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-! Kernel-checked assembly implications. A leaf bundle is a closed Prop;
no open leaf is asserted to have been proved. -/

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs

namespace AKLT.Blueprint.Rec

/-- The thirteen independent case conclusions needed for the uniform response interface. -/
structure ResponseLeaves : Prop where
  positive : StepRatioPositiveStatement
  freeUpper : FreeRatioUpperStatement
  pinnedUpper : PinnedRatioUpperStatement
  dTrivial : DStepTrivialStatement
  oneTrivial : OneStepTrivialStatement
  betaPrimePositive : BetaPrimePositiveStatement
  betaPrimeUniform : BetaPrimeUniformStatement
  twoLog : TwoLogIdentityStatement
  alphaPositive : AlphaPositiveStatement
  alphaUniform : AlphaUniformStatement
  betaPositive : BetaPositiveStatement
  betaUniform : BetaUniformStatement
  threeLog : ThreeLogIdentityStatement

/-- `l:response`: assemble the used cases without asserting an initial two-bond D expansion. -/
theorem response_of_leaves (h : ResponseLeaves) : Top.ResponseStatement := by
  intro G τ D hD y hy o ho
  let a : Departure := ⟨G, τ, D, y, o, hD, hy, ho⟩
  refine ⟨h.positive a false, h.freeUpper a, h.positive a true, h.pinnedUpper a,
    h.dTrivial a, h.oneTrivial a, ?_, ?_⟩
  · intro f hU hs hne
    exact ⟨h.betaPrimePositive a hU f hs hne, h.betaPrimeUniform a hU f hs hne,
      h.twoLog a hU f hs hne⟩
  · intro f g hU hs hof hog hfg
    exact ⟨h.alphaPositive a hU f g hs hof hog hfg, h.alphaUniform a hU f g hs hof hog hfg,
      h.betaPositive a hU f g hs hof hog hfg, h.betaUniform a hU f g hs hof hog hfg,
      h.threeLog a hU f g hs hof hog hfg⟩

/-- `l:log-mean-bounds`: combine independent coordinate monotonicities,
the two rational enclosures, and the already proved exact rows. -/
theorem logMeanBounds_of_leaves (hx : LogCoefficientMonoXStatement)
    (hy : LogCoefficientMonoYStatement) (hl : LogEnclosureLowerStatement)
    (hu : LogEnclosureUpperStatement) : Top.LogMeanBoundsStatement := by
  have mono : ∀ c : ℝ, 3 / 5 ≤ c → c ≤ 1 → ∀ x x' y y' : ℝ,
      0 < x → x ≤ x' → 0 < y → y ≤ y' →
      1 / (3 * logarithmicMean (c*x') y') - 1 / (5 * logarithmicMean x' y') ≤
        1 / (3 * logarithmicMean (c*x) y) - 1 / (5 * logarithmicMean x y) := by
    intro c hc hc1 x x' y y' hxp hxx hyp hyy
    exact (hy c x' y y' hc hc1 (lt_of_lt_of_le hxp hxx) hyp hyy).trans
      (hx c x x' y hc hc1 hxp hxx hyp)
  refine ⟨reciprocalLogMean_one, mono, ?_, fun s hs hs1 => ⟨hl s hs hs1, hu s hs hs1⟩,
    logRationalRows⟩
  intro c x y hc hc1 hx hy
  have h := mono c hc hc1 (116 / 125) x 1 y (by norm_num) hx (by norm_num) hy
  simpa [reciprocalLogMean, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h

/-- Local numeric/analytic obligations for the corrected covered matcher. -/
structure TypedLeaves : Prop where
  lower : CoveredIntegratedLowerStatement
  threeIntervals : RemovedMeanIntervalsStatement
  twoIntervals : TwoMeanIntervalsStatement
  betaPrime : BetaPrimeAnalyticStatement
  beta : BetaAnalyticStatement
  alpha : AlphaAnalyticStatement

/-- `l:response-typed`: prove the corrected, useful interface first. -/
theorem responseTypedV2_of_leaves (hR : Top.ResponseStatement)
    (hL : Top.LogMeanBoundsStatement) (h : TypedLeaves) : ResponseTypedStatementV2 := by
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

/-- The original Top statement remains a consequence because its matcher
is more restrictive than the corrected one. -/
theorem responseTyped_of_v2 (h : ResponseTypedStatementV2) : Top.ResponseTypedStatement := by
  intro hH1
  refine ⟨(h hH1).1, ?_⟩
  intro G τ D hD y hy hU a o hcov
  exact (h hH1).2 G τ D hD y hy hU a o (coveredDeparture_to_v2 hD hcov)

structure MThetaLeaves : Prop where
  regroup : KernelRegroupStatement
  lengthBound : KernelLengthMajorantStatement
  finiteMajorant : MajorantFiniteStatement
  geometry : ShiftGeometryStatement
  unshifted : UnshiftedWitnessStatement
  choice : TransportChoiceStatement
  perturbation : WitnessPerturbationStatement

/-- `l:Mtheta`: nonnegative summability followed by explicit witness transport. -/
theorem mTheta_of_leaves (h : MThetaLeaves) : Top.MThetaStatement := by
  intro CV q hOpen hH3
  have entry : ∀ θ : ℝ, q^2 < θ → θ ≤ 1 → ∀ X Y : PairType,
      shiftedKernel θ X Y ≠ ⊤ ∧ shiftedKernel θ X Y ≤
        ∑' n : ℕ, ENNReal.ofReal (kernelMajorant CV q θ n) := by
    intro θ hqθ hθ1 X Y
    rw [h.regroup θ (lt_of_le_of_lt (sq_nonneg q) hqθ) X Y]
    have hle := ENNReal.tsum_le_tsum (h.lengthBound CV q hOpen θ hqθ hθ1 X Y)
    exact ⟨lt_top_iff_ne_top.mp (lt_of_le_of_lt hle
      (lt_top_iff_ne_top.mpr (h.finiteMajorant CV q hOpen θ hqθ hθ1))), hle⟩
  obtain ⟨hθq, hθ1, hρ0, hρ1, hbθ, hbudget⟩ := h.choice CV q hOpen
  refine ⟨entry, h.geometry, transportTheta CV q, transportRho, hθq, hθ1, hρ0, hρ1, ?_⟩
  exact ⟨fun X Y => (entry _ hθq hθ1.le X Y).1,
    fun X => h.perturbation CV q hOpen _ _ hbθ hθ1.le (kernelRho_pos.trans hρ0)
      hbudget X (h.unshifted hH3 X)⟩

/-- The full bounded renewal conclusion; this is assembled below, not an open leaf. -/
def BoundedRenewalStatement : Prop :=
  ∀ m : PairType → PairType → ℕ → ℝ, ∀ h : PairType → ℝ,
    ∀ q θ ρ CT : ℝ, 0 < q → q^2 < θ → θ < 1 → 0 < ρ → ρ < 1 → 0 ≤ CT →
    RenewalRows m h θ ρ → ∀ F : PairType → ℤ → ℝ,
    (∀ X d, 0 ≤ F X d ∧ F X d ≤ 2) →
    (∀ X : PairType, ∀ d : ℕ, 1 ≤ d → F X d ≤ renewalOp m F X d + CT * q^(2*d)) →
    2 ≤ genericAmplitude h CT ρ ∧
      ∀ X : PairType, ∀ d : ℕ, F X d ≤ genericAmplitude h CT ρ * θ^d

/-- `l:renewal`: finite iteration, an unweighted remainder, a weighted
source estimate, then a scalar limit. Arbitrarily large shifts are allowed. -/
theorem boundedRenewal_of_leaves (hi : RenewalFiniteIterationStatement)
    (hr : RenewalRemainderStatement) (hs : RenewalSourceStatement)
    (hl : RenewalScalarLimitStatement) : BoundedRenewalStatement := by
  intro m h q θ ρ CT hq hqθ hθ1 hρ hρ1 hCT hrows F hF hrec
  have hθ : 0 < θ := lt_of_le_of_lt (sq_nonneg q) hqθ
  have hminp : 0 < hmin h := lt_min (hrows.2.1 .B) (hrows.2.1 .C)
  have hden : 0 < 1 - ρ := sub_pos.mpr hρ1
  have hH : 1 ≤ hmax h / hmin h := (le_div_iff₀ hminp).mpr (by
    dsimp [hmin, hmax]
    simp)
  have hC : 2 ≤ max 2 CT := le_max_left _ _
  constructor
  · dsimp [genericAmplitude]
    apply (le_div_iff₀ hden).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hH) (show 0 ≤ max 2 CT by linarith)]
  intro X d
  have hXp : 0 < h X := hrows.2.1 X
  let a := (2 / hmin h) * h X
  let b := (max 2 CT / hmin h) * h X * θ^(d : ℤ)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hscalar : F X d ≤ b / (1 - ρ) := by
    apply hl _ a b ρ ha hb hρ hρ1
    intro k
    have hsum : (∑ j ∈ Finset.range k, renewalIterate m (renewalSource CT q) j X d) ≤
        b * ∑ j ∈ Finset.range k, ρ^j := by
      calc
        _ ≤ ∑ j ∈ Finset.range k, (max 2 CT / hmin h) * ρ^j * h X * θ^(d : ℤ) :=
          Finset.sum_le_sum (fun j _ => hs m h q θ ρ CT hq hqθ hθ1 hρ hρ1 hCT hrows j X d)
        _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; dsimp [b]; ring
    calc
      F X d ≤ renewalIterate m F k X d +
          ∑ j ∈ Finset.range k, renewalIterate m (renewalSource CT q) j X d :=
        hi m h q θ ρ CT hq hqθ hθ1 hρ hρ1 hCT hrows F hF hrec k X d
      _ ≤ (2 / hmin h) * ρ^k * h X + b * ∑ j ∈ Finset.range k, ρ^j :=
        add_le_add (hr m h θ ρ hθ hθ1 hρ hρ1 hrows F hF k X d) hsum
      _ = _ := by dsimp [a]; ring
  have hX : h X ≤ hmax h := by cases X <;> simp [hmax]
  calc
    F X d ≤ b / (1 - ρ) := hscalar
    _ ≤ ((max 2 CT / hmin h) * hmax h * θ^(d : ℤ)) / (1 - ρ) := by
      apply div_le_div_of_nonneg_right _ hden.le
      apply mul_le_mul_of_nonneg_right _ (zpow_nonneg hθ.le _)
      exact mul_le_mul_of_nonneg_left hX (by positivity)
    _ = genericAmplitude h CT ρ * θ^d := by dsimp [genericAmplitude]; rw [zpow_natCast]; ring

structure RecursionLeaves : Prop where
  envelopes : EnvelopeBoundsStatement
  split : PairResponseSplitStatement
  lengthComparison : TraceKernelLengthStatement
  finiteTail : FiniteKernelTailDominationStatement
  second : SecondTermBoundStatement
  removal : RemovalEnvelopeStatement
  realRows : ShiftedRowsRealStatement

/-- `e:rec-T1`: a separate checked gluing step, so the finite trace
comparison and infinite-series conversion can be assigned independently. -/
theorem firstTermBound_of_leaves (hl : TraceKernelLengthStatement)
    (ht : FiniteKernelTailDominationStatement) (he : EnvelopeBoundsStatement) :
    FirstTermBoundStatement := by
  intro hH1 CV q hOpen p d hd hdepth
  calc
    |firstTerm p| ≤ ∑ n ∈ Finset.range (p.normalized.bonds.card + 1), |firstLength p n| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.range (p.normalized.bonds.card + 1),
        ∑ Y : PairType, ∑ s ∈ Finset.range (n + 2),
          (kernelLengthCoefficient p.X Y s n : ℝ) * responseEnvelope Y ((d : ℤ) - s) :=
      Finset.sum_le_sum (fun n _ => hl hH1 p d hd hdepth n)
    _ ≤ recursionSeries p.X d := ht CV q hOpen responseEnvelope he p.X d _

/-- `t:rec`: the remaining elementary combination of the response
recursion, Mtheta, bounded renewal, and the ordinary removal-domain realization. -/
theorem rec_of_leaves (hM : Top.MThetaStatement) (hN : BoundedRenewalStatement)
    (h : RecursionLeaves) : Top.RecStatement := by
  intro CV q hH1 hOpen hH3
  obtain ⟨_, _, θ, ρ, hqθ, hθ1, hρ0, hρ1, hshift⟩ := hM CV q hOpen hH3
  have hθ : 0 < θ := lt_of_le_of_lt (sq_nonneg q) hqθ
  have hρ : 0 < ρ := kernelRho_pos.trans hρ0
  have hCT : 0 ≤ sourceConstant CV q := by unfold sourceConstant; positivity
  have hFirst := firstTermBound_of_leaves h.lengthComparison h.finiteTail h.envelopes
  have hrec : ∀ X : PairType, ∀ d : ℕ, 1 ≤ d →
      responseEnvelope X d ≤ renewalOp realKernel responseEnvelope X d + sourceConstant CV q * q^(2*d) := by
    intro X d hd
    apply envelope_le_of_pair_bounds X d _
    · apply add_nonneg
      · exact tsum_nonneg fun j => mul_nonneg ENNReal.toReal_nonneg (h.envelopes _ _).1
      · exact mul_nonneg hCT (pow_nonneg hOpen.2.1.le _)
    intro p hp hdepth
    have hinterior : p.u ∉ protectedSites p.G ∧ p.v ∉ protectedSites p.G := by
      constructor
      · intro hu
        have hz : setDistance latticeDist p.u (↑(protectedSites p.G) : Set Plane) ≤ 0 := by
          unfold setDistance
          exact iInf_le_of_le ⟨p.u, hu⟩ (by simp [latticeDist])
        have hn := hdepth.trans ((min_le_left _ _).trans hz)
        have : d ≤ 0 := by exact_mod_cast hn
        omega
      · intro hv
        have hz : setDistance latticeDist p.v (↑(protectedSites p.G) : Set Plane) ≤ 0 := by
          unfold setDistance
          exact iInf_le_of_le ⟨p.v, hv⟩ (by simp [latticeDist])
        have hn := hdepth.trans ((min_le_right _ _).trans hz)
        have : d ≤ 0 := by exact_mod_cast hn
        omega
    change |p.response| ≤ _
    rw [h.split p hinterior.1 hinterior.2]
    calc
      |firstTerm p + secondTerm p| ≤ |firstTerm p| + |secondTerm p| := abs_add_le _ _
      _ ≤ recursionSeries p.X d + sourceConstant CV q * q^(2*d) :=
        add_le_add (hFirst hH1 CV q hOpen p d hd hdepth) (h.second hH1 CV q hOpen p d hd hdepth)
      _ = _ := by rw [hp]; rfl
  have rows := h.realRows θ ρ hθ hθ1 hρ hρ1 hshift
  obtain ⟨hA, hdecay⟩ := hN realKernel witnessReal q θ ρ (sourceConstant CV q)
    hOpen.2.1 hqθ hθ1 hρ hρ1 hCT rows responseEnvelope h.envelopes hrec
  have hAmp : genericAmplitude witnessReal (sourceConstant CV q) ρ = Top.renewalAmplitude CV q ρ := rfl
  rw [hAmp] at hA hdecay
  refine ⟨θ, ρ, hqθ, hθ1, hρ0, hρ1, hshift, hA, hθ, hθ1, ?_⟩
  intro G τ Y hY u v hu hv huv hc
  obtain ⟨X, d, hdist, hbound⟩ := h.removal G τ Y hY u v hu hv huv hc
  apply hbound.trans
  simpa [decay, hdist] using hdecay X d

/-- A direct export for the original typed Top interface. -/
theorem responseTyped_of_leaves (hR : Top.ResponseStatement)
    (hL : Top.LogMeanBoundsStatement) (h : TypedLeaves) : Top.ResponseTypedStatement :=
  responseTyped_of_v2 (responseTypedV2_of_leaves hR hL h)

/-- The entire advertised target list, with the useful corrected interface as well. -/
def TargetsStatement : Prop :=
  Top.ResponseStatement ∧ Top.LogMeanBoundsStatement ∧ Top.ResponseTypedStatement ∧
    ResponseTypedStatementV2 ∧ Top.MThetaStatement ∧ Top.RecStatement

/-- All inputs here are closed Props. Rational endpoint checks are already proved. -/
structure AssemblyLeaves : Prop where
  response : ResponseLeaves
  logX : LogCoefficientMonoXStatement
  logY : LogCoefficientMonoYStatement
  logLower : LogEnclosureLowerStatement
  logUpper : LogEnclosureUpperStatement
  typed : TypedLeaves
  matrix : MThetaLeaves
  iterate : RenewalFiniteIterationStatement
  remainder : RenewalRemainderStatement
  source : RenewalSourceStatement
  limit : RenewalScalarLimitStatement
  recursion : RecursionLeaves

/-- The five original interfaces and the corrected covered-template interface
follow from the listed closed leaves, without additional analytic assumptions. -/
theorem targets_of_leaves (h : AssemblyLeaves) : TargetsStatement := by
  have hR := response_of_leaves h.response
  have hL := logMeanBounds_of_leaves h.logX h.logY h.logLower h.logUpper
  have hT := responseTypedV2_of_leaves hR hL h.typed
  have hM := mTheta_of_leaves h.matrix
  have hN := boundedRenewal_of_leaves h.iterate h.remainder h.source h.limit
  exact ⟨hR, hL, responseTyped_of_v2 hT, hT, hM, rec_of_leaves hM hN h.recursion⟩

#print axioms response_of_leaves
#print axioms logMeanBounds_of_leaves
#print axioms responseTypedV2_of_leaves
#print axioms responseTyped_of_v2
#print axioms mTheta_of_leaves
#print axioms boundedRenewal_of_leaves
#print axioms rec_of_leaves
#print axioms responseTyped_of_leaves
#print axioms targets_of_leaves
#print axioms firstTermBound_of_leaves

end AKLT.Blueprint.Rec
