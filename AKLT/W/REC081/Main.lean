import AKLT.W.REC081.Summation
import AKLT.W.REC081.Normalization
import AKLT.Blueprint.Rec.NodesV2Closure
import AKLT.W.REC080.Main
import AKLT.W.REC094.Main
import AKLT.W.REC096.Main

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC081

/-- The common pointwise estimate with the shared present-bond matcher and
at most twelve exceptions, supplied by REC094. -/
def ResidualSharedMatcherPointwise : Prop := OnePointPointwiseStatementV2

/-- The first-hit specialization of the covered-closure estimate REC096:
every true U departure matches a shared covered pattern. -/
def ResidualFirstTrailCoverage : Prop :=
  ∀ p : PairSetup, ∀ n : ℕ, ∀ w : DirectionWord n,
    StoppedNetworkTrail p.normalized p.u (protectedSites p.G) w →
    ∀ i : Fin n,
      (prefixNetwork p.normalized p.u w i.val).status (wordVertex p.u w i.val) = .U →
      AKLT.Defs.CoveredDepartureV2 (prefixNetwork p.normalized p.u w i.val)
        (wordVertex p.u w i.val) (wordIncoming p.incoming w i) (w i)

/-- The uniform terminal scalar-product estimate REC080, with original pins,
original S, and the unchanged one-point constant. -/
def ResidualTerminalTarget : Prop := ResidualTargetBoundStatement

/-- The H2 summation step for the shared matcher follows from its pointwise
estimate alone; no one-point-sum blueprint leaf is used as a lemma. -/
theorem onePointSumV2_of_pointwise (hpoint : ResidualSharedMatcherPointwise) :
    OnePointSumStatementV2 := by
  intro hH1 CV q hOpen G τ D haux u hstart incoming habs hcount
  apply onePointSum_le_of_pointwise D τ u incoming CV q hOpen habs
  intro n w hw
  exact hpoint hH1 G τ D haux u hstart incoming habs n w hw (hcount n w hw)

theorem uncoveredCountV2_eq_zero {G : Finset Plane} {n : ℕ} (D : Network G)
    (u : Plane) (incoming : Compass) (w : DirectionWord n)
    (hcovered : ∀ i : Fin n,
      (prefixNetwork D u w i.val).status (wordVertex u w i.val) = .U →
      AKLT.Defs.CoveredDepartureV2 (prefixNetwork D u w i.val)
        (wordVertex u w i.val) (wordIncoming incoming w i) (w i)) :
    uncoveredCountV2 D u incoming w = 0 := by
  classical
  unfold uncoveredCountV2
  have hempty : (Finset.univ.filter fun i : Fin n =>
      (prefixNetwork D u w i.val).status (wordVertex u w i.val) = .U ∧
      ¬ AKLT.Defs.CoveredDepartureV2 (prefixNetwork D u w i.val)
        (wordVertex u w i.val) (wordIncoming incoming w i) (w i)) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro i _ hi
    exact hi.2 (hcovered i hi.1)
  rw [hempty, Finset.card_empty]

/-- Derive the all-first-hits sum from the pointwise and coverage estimates.
The length summation and the enlargement to the H2 trail class are proved. -/
theorem normalized_onePointSum_of_residuals
    (hpoint : ResidualSharedMatcherPointwise) (hcover : ResidualFirstTrailCoverage)
    (hH1 : AKLT.Blueprint.Top.H1Statement) (CV q : ℝ) (hOpen : OpenTrailBound CV q)
    (p : PairData) (hu : p.u ∉ protectedSites p.G) :
    onePointSum p.normalized p.τ p.u ≤
      onePointConstant CV q * q ^ protectedDistance p.G p.u := by
  obtain ⟨incoming, hin⟩ := adjacent_compass p.u p.c p.pair.2.2.2.2.2.1
  let setup : PairSetup := ⟨p, incoming, hin, hu⟩
  have habs := normalized_incoming_absent p incoming hin
  apply onePointSum_le_of_pointwise p.normalized p.τ p.u incoming CV q hOpen habs
  intro n w hw
  have hzero : uncoveredCountV2 p.normalized p.u incoming w = 0 :=
    uncoveredCountV2_eq_zero p.normalized p.u incoming w (hcover setup n w hw)
  exact hpoint hH1 p.G p.τ p.normalized (normalized_auxiliary p) p.u
    (normalized_start p hu) incoming habs n w hw (by omega)

/-- Assemble the second-term bound from its three explicit dependencies. -/
theorem main_of_residuals
    (hpoint : ResidualSharedMatcherPointwise) (hcover : ResidualFirstTrailCoverage)
    (hterminal : ResidualTerminalTarget) :
    AKLT.Blueprint.Rec.SecondTermBoundStatement := by
  intro hH1 CV q hOpen p d hd hdepth
  obtain ⟨hu, hv⟩ := pair_interior p d hd hdepth
  obtain ⟨hdu, hdv⟩ := protectedDepthProjection p d hdepth
  have hq0 : 0 ≤ q := hOpen.2.1.le
  have hq1 : q < 1 := hOpen.2.2.1
  have hconstant := onePointConstant_nonneg CV q hOpen
  have hK : 0 ≤ onePointConstant CV q * q ^ protectedDistance p.G p.v :=
    mul_nonneg hconstant (pow_nonneg hq0 _)
  have hsecond := secondTerm_le_onePointSum p _ hK
    (hterminal hH1 CV q hOpen p hu hv)
  have hsum := normalized_onePointSum_of_residuals hpoint hcover hH1 CV q hOpen p hu
  have hpow :
      q ^ protectedDistance p.G p.u * q ^ protectedDistance p.G p.v ≤ q ^ (d + d) := by
    rw [← pow_add]
    exact pow_le_pow_of_le_one hq0 hq1.le (by omega)
  have hcoef : 0 ≤ 2 * onePointConstant CV q ^ 2 := by positivity
  calc
    |secondTerm p| ≤
        (2 * (onePointConstant CV q * q ^ protectedDistance p.G p.v)) *
          onePointSum p.normalized p.τ p.u := hsecond
    _ ≤ (2 * (onePointConstant CV q * q ^ protectedDistance p.G p.v)) *
          (onePointConstant CV q * q ^ protectedDistance p.G p.u) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num) hK)
    _ = (2 * onePointConstant CV q ^ 2) *
          (q ^ protectedDistance p.G p.u * q ^ protectedDistance p.G p.v) := by ring
    _ ≤ (2 * onePointConstant CV q ^ 2) * q ^ (d + d) :=
      mul_le_mul_of_nonneg_left hpow hcoef
    _ = sourceConstant CV q * q ^ (2 * d) := by
      rw [show d + d = 2 * d by omega]
      unfold sourceConstant onePointConstant exceptionFactor
      ring

/-- Covered closure applies to all first hits of the original protected set,
including trails which visit the other endpoint before stopping. -/
theorem firstTrailCoverage : ResidualFirstTrailCoverage := by
  intro p n w hw i hU
  exact AKLT.W.REC096.main p (protectedSites p.G) n w hw i hU

/-- The second term has the retained source constant and two original-depth
decay factors, using the proved shared-matcher leaves. -/
theorem main : AKLT.Blueprint.Rec.SecondTermBoundStatement :=
  main_of_residuals AKLT.W.REC094.main firstTrailCoverage AKLT.W.REC080.main

end AKLT.W.REC081
