module
public import AKLT.W.REC091.Factorizations
public import AKLT.W.REC089.Main

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs
open AKLT.Blueprint.Rec

namespace AKLT.W.REC091

/-- The shared-cover mixture interface, discharged by the proved REC089 leaf. -/
def Residual_SharedCoverMixture : Prop :=
  AKLT.Blueprint.Rec.LocalMixtureStatementV2

/-- Exact integration of the departure spin in the two- and three-neighbour
cases. -/
def Residual_StepFactorizations : Prop :=
  AKLT.Blueprint.Rec.TwoFactorizationStatement ∧
    AKLT.Blueprint.Rec.ThreeFactorizationStatement

/-- Positivity needed to cancel the partition function after removing the
departure site. -/
def Residual_RemovedPartitionPositive : Prop :=
  ∀ a : AKLT.Blueprint.Rec.Departure,
    0 < (AKLT.Defs.removeSite a.D a.y).partition a.τ true (fun _ => 1)

theorem stepFactorizations : Residual_StepFactorizations :=
  ⟨twoFactorization, threeFactorization⟩

theorem removedPartitionPositive : Residual_RemovedPartitionPositive :=
  fun a => network_partition_pos (removeSite a.D a.y) a.τ true

/-- The common-mixture comparison before integrating the departure spin. -/
def Residual_PartitionLower : Prop :=
  AKLT.Blueprint.Top.H1Statement →
    ∀ a : AKLT.Blueprint.Rec.Departure, a.D.status a.y = .U →
    ∀ incoming outgoing : Compass, a.o = a.y + outgoing.step →
    AKLT.Defs.CoveredDepartureV2 a.D a.y incoming outgoing →
    let c : ℝ := localThreshold (decide (outgoing = incoming))
    c * (traceStep a.D a.y a.o).partition a.τ true (fun _ => 1) ≤
      a.D.partition a.τ true (fun _ => 1)

theorem partitionLower_of_sharedCoverMixture
    (hMix : Residual_SharedCoverMixture) : Residual_PartitionLower := by
  intro hH1 a hU incoming outgoing hstep hcov
  let c : ℝ := localThreshold (decide (outgoing = incoming))
  obtain ⟨k, π, m, weight, hw, hcur, hnext⟩ := hMix a hU incoming outgoing hstep hcov
  rcases hH1 with ⟨_, _, _, _, hpattern⟩
  have hterm : ∀ i : Fin k,
      c * patternNext (π i) (m i) ≤ patternCurrent (π i) (m i) := by
    intro i
    have hcoeff :
        (if (π i).outgoing = .north then (961 / 1000 : ℝ) else 187 / 200) = c := by
      by_cases hn : (π i).outgoing = .north
      · have hs : outgoing = incoming := (hw i).2.2.mp hn
        simp [c, localThreshold, hn, hs]
      · have hs : outgoing ≠ incoming := fun h => hn ((hw i).2.2.mpr h)
        simp [c, localThreshold, hn, hs]
    calc
      c * patternNext (π i) (m i) =
          (if (π i).outgoing = .north then (961 / 1000 : ℝ) else 187 / 200) *
            patternNext (π i) (m i) := by rw [hcoeff]
      _ ≤ patternCurrent (π i) (m i) := hpattern (π i) (hw i).2.1 (m i)
  have hsum :
      (∑ i : Fin k, weight i * (c * patternNext (π i) (m i))) ≤
        ∑ i : Fin k, weight i * patternCurrent (π i) (m i) := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (hterm i) (hw i).1
  calc
    c * (traceStep a.D a.y a.o).partition a.τ true (fun _ => 1) =
        ∑ i : Fin k, weight i * (c * patternNext (π i) (m i)) := by
      rw [hnext, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i : Fin k, weight i * patternCurrent (π i) (m i) := hsum
    _ = a.D.partition a.τ true (fun _ => 1) := hcur.symm

theorem main_of_residuals
    (hLower : Residual_PartitionLower)
    (hFact : Residual_StepFactorizations)
    (hPos : Residual_RemovedPartitionPositive) :
    AKLT.Blueprint.Rec.CoveredIntegratedLowerStatementV2 := by
  intro hH1 a hU incoming outgoing hstep hcov
  let c : ℝ := localThreshold (decide (outgoing = incoming))
  have hpart := hLower hH1 a hU incoming outgoing hstep hcov
  refine ⟨?_, ?_⟩
  · intro f hneigh hne
    rcases hFact.1 a hU f hneigh hne true with ⟨hbefore, hafter⟩
    rw [hbefore, hafter] at hpart
    have hmul :
        (removeSite a.D a.y).partition a.τ true (fun _ => 1) * c ≤
          (removeSite a.D a.y).partition a.τ true (fun _ => 1) *
            responseI₂ a.D a.τ true a.y a.o f := by
      nlinarith [hpart]
    exact le_of_mul_le_mul_left hmul (hPos a)
  · intro f g hneigh hof hog hfg
    rcases hFact.2 a hU f g hneigh hof hog hfg true with ⟨hbefore, hafter⟩
    rw [hbefore, hafter] at hpart
    have hmul :
        (removeSite a.D a.y).partition a.τ true (fun _ => 1) *
            (c * responseJ a.D a.τ true a.y f g) ≤
          (removeSite a.D a.y).partition a.τ true (fun _ => 1) *
            responseI a.D a.τ true a.y a.o f g := by
      nlinarith [hpart]
    exact le_of_mul_le_mul_left hmul (hPos a)

theorem main_from_core_residuals
    (hMix : Residual_SharedCoverMixture)
    (hFact : Residual_StepFactorizations)
    (hPos : Residual_RemovedPartitionPositive) :
    AKLT.Blueprint.Rec.CoveredIntegratedLowerStatementV2 :=
  main_of_residuals (partitionLower_of_sharedCoverMixture hMix) hFact hPos

theorem main_of_partitionLower (hLower : Residual_PartitionLower) :
    AKLT.Blueprint.Rec.CoveredIntegratedLowerStatementV2 :=
  main_of_residuals hLower stepFactorizations removedPartitionPositive

/-- Combine a shared-cover mixture with the departure integration and positivity
proved in this directory. -/
theorem main_of_sharedCoverMixture (hMix : Residual_SharedCoverMixture) :
    AKLT.Blueprint.Rec.CoveredIntegratedLowerStatementV2 :=
  main_of_partitionLower (partitionLower_of_sharedCoverMixture hMix)

/-- H1 gives the integrated lower bounds with the unchanged straight/turn
Boolean and canonical response scalars. REC089 supplies the shared mixture. -/
theorem main : AKLT.Blueprint.Rec.CoveredIntegratedLowerStatementV2 :=
  main_of_sharedCoverMixture AKLT.W.REC089.main

#print axioms partitionLower_of_sharedCoverMixture
#print axioms main_of_residuals
#print axioms main_from_core_residuals
#print axioms stepFactorizations
#print axioms removedPartitionPositive
#print axioms main_of_sharedCoverMixture
#print axioms main_of_partitionLower
#print axioms main

end AKLT.W.REC091
