module
public import AKLT.W.REC079.OrderedExposure

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-! REC079: fixed-chart trace comparison with the exact type-dependent kernel.
Both local obligations in the earlier reduction are discharged by proved leaves
and the local comparisons in this directory. -/

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs AKLT.Blueprint.Rec AKLT.Cert.H2

namespace AKLT.W.REC079

attribute [local instance] Classical.propDecidable

/-- Triangle inequality followed by the fixed injective map on words assembles
the pointwise comparison. All omitted canonical trails have nonnegative budget. -/
theorem main_from_residuals (hexposure : Residual_OrderedExposureV2)
    (hlocal : Residual_LocalEnvelopeV2) : AKLT.Blueprint.Rec.TraceKernelLengthStatement := by
  intro hH1 p d hd hdepth n
  have hs : firstLength p n =
      ∑ w ∈ stoppedNetworkTrails p.normalized p.u (insert p.v (protectedSites p.G)) n,
        if wordVertex p.u w n = p.v then targetSummand p w else 0 := rfl
  rw [hs]
  calc
    |∑ w ∈ stoppedNetworkTrails p.normalized p.u (insert p.v (protectedSites p.G)) n,
        if wordVertex p.u w n = p.v then targetSummand p w else 0| ≤
      ∑ w ∈ stoppedNetworkTrails p.normalized p.u (insert p.v (protectedSites p.G)) n,
        |if wordVertex p.u w n = p.v then targetSummand p w else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ w : DirectionWord n, if ClosedTrail p.X w then canonicalBudget p.X d w else 0 := by
      apply Finset.sum_le_sum_of_injOn (canonicalWord p)
        (canonicalWord_injective p n).injOn (Finset.subset_univ _)
      · intro w hw
        have htrail : StoppedNetworkTrail p.normalized p.u (insert p.v (protectedSites p.G)) w :=
          (Finset.mem_filter.mp hw).2
        by_cases hend : wordVertex p.u w n = p.v
        · have hc := target_trail_closed p w htrail hend
          simp only [hend, ite_true, hc]
          exact targetSummand_le_budget hexposure hlocal hH1 p d hd hdepth w htrail hend
        · simp only [hend, ite_false, abs_zero]
          split_ifs
          · exact canonicalBudget_nonneg _ _ _
          · rfl
      · intro w _ _
        split_ifs
        · exact canonicalBudget_nonneg _ _ _
        · rfl
    _ = ∑ Y : PairType, ∑ s ∈ Finset.range (n + 2),
        (kernelLengthCoefficient p.X Y s n : ℝ) * responseEnvelope Y ((d : ℤ) - s) :=
      (kernel_bound_eq_sum p.X d n).symm

private theorem no_closedTrail_zero : ∀ X : PairType, ∀ w : DirectionWord 0, ¬ ClosedTrail X w := by
  intro X w h
  have he := h.2.1
  cases X <;> norm_num [wordVertex, kernelStart, kernelTarget] at he

private theorem no_closedTrail_one : ∀ X : PairType, ∀ w : DirectionWord 1, ¬ ClosedTrail X w := by
  intro X w h
  have he := h.2.1
  cases X <;> cases hw : w 0 <;>
    norm_num [wordVertex, kernelStart, kernelTarget, Fin.sum_univ_one, hw, Compass.step] at he

/-- If the canonical class is empty, every original target summand is zero. -/
theorem firstLength_eq_zero_of_no_closedTrail (p : PairData) (n : ℕ)
    (hn : ∀ w : DirectionWord n, ¬ ClosedTrail p.X w) : firstLength p n = 0 := by
  unfold firstLength
  apply Finset.sum_eq_zero
  intro w hw
  by_cases hend : wordVertex p.u w n = p.v
  · exact False.elim (hn _ (target_trail_closed p w (Finset.mem_filter.mp hw).2 hend))
  · simp [hend]

/-- The frozen inequality is unconditional at lengths zero and one. -/
theorem traceKernelLength_small (p : PairData) (d n : ℕ) (hn : n ≤ 1) :
    |firstLength p n| ≤ ∑ Y : PairType, ∑ s ∈ Finset.range (n + 2),
      (kernelLengthCoefficient p.X Y s n : ℝ) * responseEnvelope Y ((d : ℤ) - s) := by
  have hnone : ∀ w : DirectionWord n, ¬ ClosedTrail p.X w := by
    have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl
    · exact no_closedTrail_zero p.X
    · exact no_closedTrail_one p.X
  rw [firstLength_eq_zero_of_no_closedTrail p n hnone, kernel_bound_eq_sum]
  simp [hnone]

/-- The frozen length-by-length trace-to-kernel comparison. -/
theorem main : AKLT.Blueprint.Rec.TraceKernelLengthStatement :=
  main_from_residuals ordered_exposure local_envelope

end AKLT.W.REC079

#print axioms AKLT.W.REC079.main_from_residuals
#print axioms AKLT.W.REC079.traceKernelLength_small
#print axioms AKLT.W.REC079.main
