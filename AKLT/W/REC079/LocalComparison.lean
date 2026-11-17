module
public import AKLT.W.REC079.Ordering

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs AKLT.Blueprint.Rec AKLT.Cert.H2

namespace AKLT.W.REC079

attribute [local instance] Classical.propDecidable

/-- The absolute pinned-minus-free response of an unordered two-element set.
The order selected by toList does not affect the scalar product. Other set
sizes are assigned zero, and never occur in responsePairs. -/
def pairSignal {G : Finset Plane} (E : Network G) (τ : PinAssignment G) (p : Finset Plane) : ℝ :=
  match p.toList with
  | [a, b] => |E.expectation τ true (fun n => dot (n a) (n b)) -
      E.expectation τ false (fun n => dot (n a) (n b))|
  | _ => 0

theorem pairSignal_nonneg {G : Finset Plane} (E : Network G) (τ : PinAssignment G)
    (p : Finset Plane) : 0 ≤ pairSignal E τ p := by
  unfold pairSignal
  split <;> positivity

/-- Actual response at a prefix, but indexed by the fixed chart's live kernel
pairs. An actual removed endpoint gives response zero. Only true U departures
carry a response reward. -/
def localResponseReward (p : PairData) {n : ℕ} (w : DirectionWord n) (i : Fin n) : ℝ :=
  let E := prefixNetwork p.normalized p.u w i.val
  let y := wordVertex p.u w i.val
  if E.status y = .U then
    ∑ q ∈ responsePairs (canonicalWord p w) i,
      (pairCoefficient (canonicalWord p w) i q : ℝ) *
        pairSignal (removeSite E y) p.τ (q.image (canonicalChart p).point.symm)
  else 0

/-- Residual 1: ordered logarithmic exposure and the repaired type-dependent
local response comparison for ONE true trace. It is independent of depth and
of the response envelope. The ordering is exactly kernelOrdering of the fixed
canonical word, including its short/long split; extra initial D departures
have zero reward. This must be derived from H1, with the internal-bond matcher
Top.ResponseTypedStatementV2 and the non-arrival-only closure scope. -/
def Residual_OrderedExposureV2 : Prop :=
  AKLT.Blueprint.Top.H1Statement → ∀ p : PairData, ∀ n : ℕ, ∀ w : DirectionWord n,
    StoppedNetworkTrail p.normalized p.u (insert p.v (protectedSites p.G)) w →
    wordVertex p.u w n = p.v →
    |traceRatio p.normalized p.τ true (wordVertices p.u w) -
      traceRatio p.normalized p.τ false (wordVertices p.u w)| ≤
      realExposure (canonicalWord p w) (localResponseReward p w)
        (kernelOrdering (canonicalWord p w))

/-- Residual 2: ordinary response-pair closure, actual-shift transport, and the
bounded-supremum upper bound for ONE live pair at ONE true U departure. Only
non-arrival kernel pairs occur. Kernel-live endpoints that are actually
removed contribute zero through pairSignal. No local logarithmic coefficient,
exposure ordering, or sum over trails occurs in this obligation. -/
def Residual_LocalEnvelopeV2 : Prop :=
  ∀ p : PairData, ∀ d : ℕ, 1 ≤ d → (d : ℕ∞) ≤ p.depth →
    ∀ n : ℕ, ∀ w : DirectionWord n,
    StoppedNetworkTrail p.normalized p.u (insert p.v (protectedSites p.G)) w →
    wordVertex p.u w n = p.v → ∀ i : Fin n,
    (prefixNetwork p.normalized p.u w i.val).status (wordVertex p.u w i.val) = .U →
    ∀ q ∈ responsePairs (canonicalWord p w) i,
      pairSignal (removeSite (prefixNetwork p.normalized p.u w i.val)
        (wordVertex p.u w i.val)) p.τ (q.image (canonicalChart p).point.symm) ≤
      responseEnvelope (responsePairType q) ((d : ℤ) - pairShift p.X q)

theorem localResponseReward_nonneg (p : PairData) {n : ℕ} (w : DirectionWord n) (i : Fin n) :
    0 ≤ localResponseReward p w i := by
  unfold localResponseReward
  dsimp only
  split_ifs
  · exact Finset.sum_nonneg fun q _ => mul_nonneg
      (Rat.cast_nonneg.mpr (pairCoefficient_nonneg _ _ _)) (pairSignal_nonneg _ _ _)
  · rfl

/-- The local envelope residual gives pointwise reward domination. -/
theorem localResponseReward_le (hlocal : Residual_LocalEnvelopeV2)
    (p : PairData) (d : ℕ) (hd : 1 ≤ d) (hdepth : (d : ℕ∞) ≤ p.depth)
    {n : ℕ} (w : DirectionWord n)
    (hw : StoppedNetworkTrail p.normalized p.u (insert p.v (protectedSites p.G)) w)
    (hend : wordVertex p.u w n = p.v) (i : Fin n) :
    localResponseReward p w i ≤ indexedReward p.X d (canonicalWord p w) i := by
  unfold localResponseReward
  dsimp only
  split_ifs with hU
  · rw [indexedReward_eq_pairReward]
    apply Finset.sum_le_sum
    intro q hq
    exact mul_le_mul_of_nonneg_left (hlocal p d hd hdepth n w hw hend i hU q hq)
      (Rat.cast_nonneg.mpr (pairCoefficient_nonneg _ _ _))
  · exact indexedReward_nonneg _ _ _ _

/-- The pin-independent target law factor can only decrease a term. -/
theorem targetFactor_bounds {G : Finset Plane} (D : Network G) (v : Plane) :
    0 ≤ targetFactor D v ∧ targetFactor D v ≤ 1 := by
  unfold targetFactor
  split_ifs <;> norm_num

/-- A single summand before the endpoint indicator. -/
def targetSummand (p : PairData) {n : ℕ} (w : DirectionWord n) : ℝ :=
  (traceCoefficient p.normalized (wordVertices p.u w) : ℝ) *
    (traceRatio p.normalized p.τ true (wordVertices p.u w) -
      traceRatio p.normalized p.τ false (wordVertices p.u w)) * targetFactor p.D p.v

/-- The two explicitly local residuals imply the full pointwise trace-to-kernel
comparison; the base-weight inequality and target factor are proved here. -/
theorem targetSummand_le_budget (hexposure : Residual_OrderedExposureV2)
    (hlocal : Residual_LocalEnvelopeV2) (hH1 : AKLT.Blueprint.Top.H1Statement)
    (p : PairData) (d : ℕ) (hd : 1 ≤ d) (hdepth : (d : ℕ∞) ≤ p.depth)
    {n : ℕ} (w : DirectionWord n)
    (hw : StoppedNetworkTrail p.normalized p.u (insert p.v (protectedSites p.G)) w)
    (hend : wordVertex p.u w n = p.v) :
    |targetSummand p w| ≤ canonicalBudget p.X d (canonicalWord p w) := by
  have ha : (0 : ℝ) ≤ (traceCoefficient p.normalized (wordVertices p.u w) : ℝ) :=
    Rat.cast_nonneg.mpr (traceCoefficient_nonneg _ _)
  have hab : (traceCoefficient p.normalized (wordVertices p.u w) : ℝ) ≤
      (trailBaseWeight kernelStart (canonicalWord p w) : ℝ) := by
    rw [canonicalWord_baseWeight]
    exact Rat.cast_le.mpr (traceCoefficient_le_baseWeight _ _ _)
  have hf := targetFactor_bounds p.D p.v
  have he := (hexposure hH1 p n w hw hend).trans
    (realExposure_mono (canonicalWord p w) _ _
      (localResponseReward_le hlocal p d hd hdepth w hw hend) _)
  calc
    |targetSummand p w| = (traceCoefficient p.normalized (wordVertices p.u w) : ℝ) *
        |traceRatio p.normalized p.τ true (wordVertices p.u w) -
          traceRatio p.normalized p.τ false (wordVertices p.u w)| * targetFactor p.D p.v := by
      rw [targetSummand, abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hf.1]
    _ ≤ (traceCoefficient p.normalized (wordVertices p.u w) : ℝ) *
        |traceRatio p.normalized p.τ true (wordVertices p.u w) -
          traceRatio p.normalized p.τ false (wordVertices p.u w)| :=
      mul_le_of_le_one_right (mul_nonneg ha (abs_nonneg _)) hf.2
    _ ≤ canonicalBudget p.X d (canonicalWord p w) :=
      mul_le_mul hab he (abs_nonneg _) (Rat.cast_nonneg.mpr (trailBaseWeight_nonneg _ _))

end AKLT.W.REC079
