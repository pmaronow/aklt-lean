module
public import AKLT.W.REC013.Positive
public import AKLT.W.REC013.Eliminate

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC013

/-- Integrating a D departure deletes its only bond and leaves either partition unchanged. -/
theorem d_step_partition (a : AKLT.Blueprint.Rec.Departure) (hD : a.D.status a.y = .D)
    (b : Bool) :
    (traceStep a.D a.y a.o).partition a.τ b (fun _ => 1) =
      a.D.partition a.τ b (fun _ => 1) := by
  have hc : (a.D.presentNeighbors a.y).card ≤ 1 := by
    rcases a.start.2.2 with h | h
    · rw [hD] at h
      cases h.1
    · exact h.2
  have hs : a.D.presentNeighbors a.y = {a.o} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨a.present, ?_⟩
    intro z hz
    exact (Finset.card_le_one.mp hc) z hz a.o a.present
  rw [trace_partition_eq_remove a.D a.τ b a.y a.o hD]
  exact (d_partition_eq_remove a.D a.τ b a.y a.o a.start.1 a.start.2.1 hD hs).symm

/-- The D departure has ratio one for both choices of original pins. -/
theorem main : AKLT.Blueprint.Rec.DStepTrivialStatement := by
  intro a hD
  have h (b : Bool) : stepRatio a.D a.τ b a.y a.o = 1 := by
    change (traceStep a.D a.y a.o).partition a.τ b (fun _ => 1) /
      a.D.partition a.τ b (fun _ => 1) = 1
    rw [d_step_partition a hD b]
    exact div_self (ne_of_gt (partition_positive a.D a.τ a.auxiliary b))
  exact ⟨h true, h false⟩

end AKLT.W.REC013

#print axioms AKLT.W.REC013.main
