module
public import AKLT.W.REC005.Network

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC005

/-- The two-neighbor response interval, with its free lower bound. -/
theorem main : AKLT.Blueprint.Rec.TwoMeanIntervalsStatement := by
  intro a _hU f hN hne
  have hf : f ∈ a.D.presentNeighbors a.y := by rw [hN]; simp
  have ho : a.o ∈ a.D.presentNeighbors a.y := a.present
  have hbound (b : Bool) := removed_pair_bound a.D a.τ a.y f a.o
    a.start.1 a.start.2.1 hf ho (Ne.symm hne) b
  constructor
  · intro b
    have h := hbound b
    change 22 / 25 ≤ 1 + removedPairMean a.D a.τ b a.y f a.o / 3 ∧
      1 + removedPairMean a.D a.τ b a.y f a.o / 3 ≤ 28 / 25
    constructor <;> linarith
  · have h := free_pair_mean_nonneg (removeSite a.D a.y) a.τ f a.o
    change 1 ≤ 1 + removedPairMean a.D a.τ false a.y f a.o / 3
    change 0 ≤ removedPairMean a.D a.τ false a.y f a.o at h
    linarith

#print axioms AKLT.W.REC005.main

end AKLT.W.REC005
