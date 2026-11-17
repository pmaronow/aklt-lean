module
public import AKLT.W.REC082.IndependentSite

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC082

/-- The terminal numerator has the common factor 1 or 3/5. This is an
unnormalized identity and needs no claim that the remaining mass is positive. -/
theorem target_partition_factor (p : PairData) (hv : p.v ∉ protectedSites p.G)
    (n : ℕ) (w : DirectionWord n)
    (hw : StoppedNetworkTrail p.normalized p.u (insert p.v (protectedSites p.G)) w)
    (he : wordVertex p.u w n = p.v) (b : Bool) :
    (traceNetwork p.normalized (wordVertices p.u w)).partition p.τ b
        (fun a => normSq (a p.v)) =
      targetFactor p.D p.v *
        (traceNetwork p.normalized (wordVertices p.u w)).partition p.τ b (fun _ => 1) := by
  classical
  let E := traceNetwork p.normalized (wordVertices p.u w)
  have hstatus : E.status p.v = p.D.status p.v := stopped_target_status hw
  have ha : p.v ∈ E.active := by
    apply Finset.mem_filter.mpr
    have hvactive := Finset.mem_filter.mp (pair_v_active p)
    exact ⟨hvactive.1, by rw [hstatus]; exact hvactive.2⟩
  rcases p.pair.2.2.2.2.2.2.2.2.2 with hU | ⟨hD, hdeg⟩
  · have h := partition_norm_U E p.τ b p.v ha (hstatus.trans hU)
    simpa [targetFactor, hU] using h
  · have hdeg' : (p.normalized.presentNeighbours p.v).card ≤ 1 := by
      simpa only [PairData.normalized,
        normalizeStart_presentNeighbours p.D p.u p.c p.v (pair_c_removed p)] using hdeg
    have hiso : E.presentNeighbours p.v = ∅ :=
      stopped_target_isolated (pair_ne p) hdeg' hw he
    have h := partition_norm_D E p.τ b p.v ha (hstatus.trans hD) hiso hv
    simpa [targetFactor, hD] using h

/-- Exactly the weighted, pin-independent terminal identity needed in T₁. -/
theorem target_weighted_factor (p : PairData) (hv : p.v ∉ protectedSites p.G)
    (n : ℕ) (w : DirectionWord n)
    (hw : StoppedNetworkTrail p.normalized p.u (insert p.v (protectedSites p.G)) w)
    (he : wordVertex p.u w n = p.v) (b : Bool) :
    traceRatio p.normalized p.τ b (wordVertices p.u w) *
      (traceNetwork p.normalized (wordVertices p.u w)).expectation p.τ b
        (fun a => dot (a p.v) (a p.v)) =
      traceRatio p.normalized p.τ b (wordVertices p.u w) * targetFactor p.D p.v :=
  traceRatio_mul_terminal_of_partition p.normalized p.τ b (wordVertices p.u w) p.v
    (targetFactor p.D p.v) (target_partition_factor p hv n w hw he b)

end AKLT.W.REC082
