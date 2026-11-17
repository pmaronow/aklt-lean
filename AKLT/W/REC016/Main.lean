module
public import AKLT.W.REC016.Intervals

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section

namespace AKLT.W.REC016

/-- The uniform two-neighbor response coefficient in §6, lines 393–408. -/
theorem main : AKLT.Blueprint.Rec.BetaPrimeUniformStatement := by
  intro a _ f hPresent hne
  obtain ⟨hPinned, hFree⟩ := two_mean_lower a f hPresent hne
  exact coefficient_bound_of_intervals hPinned hFree

#print axioms main

end AKLT.W.REC016
