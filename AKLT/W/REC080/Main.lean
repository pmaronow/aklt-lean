import AKLT.W.REC080.Pointwise
import AKLT.W.REC043.Main
import AKLT.W.REC090.Main

/-!
The terminal geometry, shared matcher, twelve-exception count, common
pointwise majorant, and geometric summation reduce REC080 to the finite
pair expansion and shared local ratio comparison. REC043 and REC090
discharge these two dependencies and give the closed `main` theorem.
-/

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC080

/-- The second finite pair expansion, specialized to the terminal auxiliary
network. This is an identity, with no H1/H2 or decay conclusion. -/
def ResidualSecondExpansion : Prop :=
  ∀ p : PairData, p.u ∉ protectedSites p.G → p.v ∉ protectedSites p.G →
  ∀ n : ℕ, ∀ w : DirectionWord n,
    StoppedNetworkTrail p.normalized p.u (insert p.v (protectedSites p.G)) w →
    wordVertex p.u w n ∈ protectedSites p.G → ∀ b : Bool,
    let E := terminalNetwork p w
    let e := wordVertex p.u w n
    E.expectation p.τ b (fun a => dot (a p.v) (a e)) =
      stoppedSum E p.v (protectedSites p.G) fun m w' =>
        (traceCoefficient E (wordVertices p.v w') : ℝ) *
          traceRatio E p.τ b (wordVertices p.v w') *
          (traceNetwork E (wordVertices p.v w')).expectation p.τ b
            (fun a => dot (a (wordVertex p.v w' m)) (a e))

/-- A one-step local comparison, with the shared present-bond matcher.
This transparent residual is exactly `CoveredRatioStatementV2`, rather than
a new terminal decay or trace-majorant assumption. -/
def ResidualCoveredRatio : Prop :=
  AKLT.Blueprint.Top.H1Statement → ∀ a : Departure, a.D.status a.y = .U →
    ∀ incoming outgoing : Compass, a.o = a.y + outgoing.step →
      AKLT.Defs.CoveredDepartureV2 a.D a.y incoming outgoing →
      stepRatio a.D a.τ true a.y a.o ≤
        (passageFactor (decide (outgoing = incoming)) : ℝ)

/-- All admissibility premises are discharged. The target is the first
protected hit, so inserting it into S does not change the stopping set. -/
theorem secondExpansion_of_pairwalk (hWalk : PairExpansionStatement) :
    ResidualSecondExpansion := by
  intro p hu hv n w hw he b
  have hne : p.v ≠ wordVertex p.u w n := by
    intro h
    exact hv (h ▸ he)
  have h := hWalk p.G p.τ (terminalNetwork p w) (terminal_auxiliary p hu w hw he)
    p.v (wordVertex p.u w n) (terminal_start_admissible p hv w hw)
    (terminal_target_admissible p hu w hw he) hne b
  simpa only [Finset.insert_eq_of_mem he] using h

theorem terminal_expansion_bound (hExpansion : ResidualSecondExpansion)
    (p : PairData) (hu : p.u ∉ protectedSites p.G) (hv : p.v ∉ protectedSites p.G)
    {n : ℕ} (w : DirectionWord n)
    (hw : StoppedNetworkTrail p.normalized p.u (insert p.v (protectedSites p.G)) w)
    (he : wordVertex p.u w n ∈ protectedSites p.G) (b : Bool) :
    |(traceNetwork p.normalized (wordVertices p.u w)).expectation p.τ b
      (fun a => dot (a (wordVertex p.u w n)) (a p.v))| ≤
        onePointSum (terminalNetwork p w) p.τ p.v := by
  rw [← terminal_expectation p w b]
  have hobs : (fun a : Plane → Vec3 => dot (a (wordVertex p.u w n)) (a p.v)) =
      (fun a : Plane → Vec3 => dot (a p.v) (a (wordVertex p.u w n))) := by
    funext a
    exact dot_comm _ _
  rw [hobs]
  exact expansion_abs_le_onePoint (terminalNetwork p w) p.τ p.v
    (wordVertex p.u w n) b (hExpansion p hu hv n w hw he b)

/-- Shared-matcher exceptions can occur at any second-trail position;
all are counted, and the incoming direction is fixed before choosing it. -/
theorem terminal_shared_exception_bound (p : PairData)
    (hu : p.u ∉ protectedSites p.G) (hv : p.v ∉ protectedSites p.G)
    {n : ℕ} (w : DirectionWord n)
    (hw : StoppedNetworkTrail p.normalized p.u (insert p.v (protectedSites p.G)) w)
    (he : wordVertex p.u w n ∈ protectedSites p.G)
    (incoming : Compass) (hi : p.v = p.c + incoming.step)
    {m : ℕ} (w' : DirectionWord m)
    (hw' : StoppedNetworkTrail (terminalNetwork p w) p.v (protectedSites p.G) w') :
    uncoveredCountV2 (terminalNetwork p w) p.v incoming w' ≤ 12 := by
  obtain ⟨firstIncoming, hfirst⟩ := adjacent_direction p.pair.2.2.2.2.2.1
  let ps : PairSetup := ⟨p, firstIncoming, hfirst, hu⟩
  exact terminal_exception_count ps hv n w hw he incoming hi m w' hw'

theorem terminal_tail_bound (hCovered : ResidualCoveredRatio)
    (hH1 : AKLT.Blueprint.Top.H1Statement) {CV q : ℝ} (hOpen : OpenTrailBound CV q)
    (p : PairData) (hu : p.u ∉ protectedSites p.G) (hv : p.v ∉ protectedSites p.G)
    {n : ℕ} (w : DirectionWord n)
    (hw : StoppedNetworkTrail p.normalized p.u (insert p.v (protectedSites p.G)) w)
    (he : wordVertex p.u w n ∈ protectedSites p.G) :
    onePointSum (terminalNetwork p w) p.τ p.v ≤
      onePointConstant CV q * q^(protectedDistance p.G p.v) := by
  obtain ⟨incoming, hi⟩ := adjacent_direction p.pair.2.2.2.2.2.2.1
  apply onePointSum_le_of_pointwise hOpen (terminalNetwork p w) p.τ p.v incoming
    (terminal_absent p w incoming hi)
  intro m w' hw'
  exact onePointPointwise_of_coveredRatio hCovered hH1 p.G p.τ (terminalNetwork p w)
    (terminal_auxiliary p hu w hw he) p.v (terminal_start_admissible p hv w hw)
    incoming (terminal_absent p w incoming hi) m w' hw'
    (terminal_shared_exception_bound p hu hv w hw he incoming hi w' hw')

/-- Assemble the terminal expansion and the common geometric tail bound. -/
theorem main_of_residuals (hExpansion : ResidualSecondExpansion)
    (hCovered : ResidualCoveredRatio) :
    AKLT.Blueprint.Rec.ResidualTargetBoundStatement := by
  intro hH1 CV q hOpen p hu hv n w hw he b
  exact (terminal_expansion_bound hExpansion p hu hv w hw he b).trans
    (terminal_tail_bound hCovered hH1 hOpen p hu hv w hw he)

/-- Exact reduction to the two previously proved blueprint leaves. -/
theorem main_of_dependencies (hWalk : PairExpansionStatement)
    (hCovered : CoveredRatioStatementV2) :
    AKLT.Blueprint.Rec.ResidualTargetBoundStatement :=
  main_of_residuals (secondExpansion_of_pairwalk hWalk) hCovered

/-- The second pair expansion supplied by REC043. -/
theorem secondExpansion : ResidualSecondExpansion :=
  secondExpansion_of_pairwalk AKLT.W.REC043.main

/-- The shared-matcher ratio comparison supplied by REC090. -/
theorem coveredRatio : ResidualCoveredRatio :=
  AKLT.W.REC090.main

/-- The terminal residual bound, using the original protected distance. -/
theorem main : AKLT.Blueprint.Rec.ResidualTargetBoundStatement :=
  main_of_residuals secondExpansion coveredRatio

end AKLT.W.REC080
