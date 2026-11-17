module
public import AKLT.W.REC018.Network
public import AKLT.W.REC018.LogMean

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open AKLT.Defs

namespace AKLT.W.REC018

/-- Positivity follows from the unit-ball comparison `3 I ≤ 5 J`, with
strictness in the free network. Only one distinct pair is needed. -/
theorem responseAlpha_positive {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (y o f g : Plane) (hfo : f ≠ o) : 0 < responseAlpha D τ y o f g := by
  unfold responseAlpha responseBeta
  exact alpha_of_comparison _ _ _ _
    (responseI_pos D τ true y o f g) (responseI_pos D τ false y o f g)
    (responseJ_pos D τ true y f g) (responseJ_pos D τ false y f g)
    (response_compare D τ true y o f g) (free_response_compare D τ y o f g hfo)

theorem main : AKLT.Blueprint.Rec.AlphaPositiveStatement := by
  intro a _ f g _ hof _ _
  exact responseAlpha_positive a.D a.τ a.y a.o f g (Ne.symm hof)

end AKLT.W.REC018
