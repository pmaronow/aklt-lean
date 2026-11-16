import AKLT.W.REC082.Terminal
import AKLT.W.REC082.LocalMoments
import AKLT.W.REC082.PE.Main

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC082

/-- The remaining obligation is the unnormalized finite expansion at a
normalized response pair. It contains neither division by partition functions,
the terminal factor, normalization invariance, nor the response subtraction. -/
def Residual_FiniteNumeratorExpansion : Prop :=
  ∀ p : PairData, p.u ∉ protectedSites p.G → p.v ∉ protectedSites p.G →
    ∀ b : Bool,
      p.normalized.partition p.τ b (fun a => dot (a p.u) (a p.v)) =
        stoppedSum p.normalized p.u (insert p.v (protectedSites p.G))
          (fun n w =>
            (traceCoefficient p.normalized (wordVertices p.u w) : ℝ) *
              (traceNetwork p.normalized (wordVertices p.u w)).partition p.τ b
                (fun a => dot (a (wordVertex p.u w n)) (a p.v)))

/-- The finite numerator expansion, from the unnormalized stopped pair-walk
expansion `PE.pair_unnormalized` (a copy of the proved leaf REC043, with its
local contraction `PE.coordinateStep`) applied to the normalized network. -/
theorem finiteNumeratorExpansion : Residual_FiniteNumeratorExpansion := by
  intro p hu hv b
  exact PE.pair_unnormalized PE.coordinateStep p.τ p.normalized
    (normalized_auxiliary p) p.u p.v (normalized_start p hu) (normalized_target p hv) b

/-- Divide the numerator expansion once and insert the trace ratios. All
zero-denominator cases follow from nonnegative finite weights. -/
theorem onePinExpansion_of_residual (hExpansion : Residual_FiniteNumeratorExpansion)
    (p : PairData) (hu : p.u ∉ protectedSites p.G) (hv : p.v ∉ protectedSites p.G)
    (b : Bool) :
    p.D.expectation p.τ b (fun a => dot (a p.u) (a p.v)) =
      stoppedSum p.normalized p.u (insert p.v (protectedSites p.G))
        (fun n w =>
          (traceCoefficient p.normalized (wordVertices p.u w) : ℝ) *
            traceRatio p.normalized p.τ b (wordVertices p.u w) *
              (traceNetwork p.normalized (wordVertices p.u w)).expectation p.τ b
                (fun a => dot (a (wordVertex p.u w n)) (a p.v))) := by
  rw [← normalized_expectation p b]
  conv_lhs => unfold Network.expectation
  rw [hExpansion p hu hv b]
  unfold stoppedSum
  simp only [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro w _
  rw [mul_assoc, traceRatio_mul_expectation]
  ring

/-- The finite target/boundary split, with the terminal and normalization
identities proved in this directory and just the finite numerator expansion
left as an explicit closed residual. -/
theorem main_of_residual (hExpansion : Residual_FiniteNumeratorExpansion) :
    PairResponseSplitStatement := by
  intro p hu hv
  classical
  have hexp (b : Bool) := onePinExpansion_of_residual hExpansion p hu hv b
  change
    p.D.expectation p.τ true (fun a => dot (a p.u) (a p.v)) -
        p.D.expectation p.τ false (fun a => dot (a p.u) (a p.v)) =
      firstTerm p + secondTerm p
  rw [hexp true, hexp false]
  unfold firstTerm firstLength secondTerm stoppedSum
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  by_cases he : wordVertex p.u w n = p.v
  · have hwt : StoppedNetworkTrail p.normalized p.u (insert p.v (protectedSites p.G)) w :=
      (Finset.mem_filter.mp hw).2
    simp only [he, ite_true]
    rw [mul_assoc, target_weighted_factor p hv n w hwt he true,
      mul_assoc, target_weighted_factor p hv n w hwt he false]
    ring
  · simp only [he, ite_false]
    ring

/-- The target/boundary split of the pair response. -/
theorem main : PairResponseSplitStatement :=
  main_of_residual finiteNumeratorExpansion

end AKLT.W.REC082
