module
public import AKLT.W.REC004.Free
public import AKLT.W.REC004.FibreExpansion
public import AKLT.W.REC004.Expansion

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC004

/-- The free inequalities of the target need no additional premise. -/
theorem free_response_comparison {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (y o f g : Plane) :
    1 ≤ responseJ D τ false y f g ∧
      responseJ D τ false y f g ≤ responseI D τ false y o f g := by
  have hfg := removedPairMean_free_nonneg D τ y f g
  have hfo := removedPairMean_free_nonneg D τ y f o
  have hgo := removedPairMean_free_nonneg D τ y g o
  dsimp [responseI, responseJ]
  constructor <;> linarith

/-- Reduction of the frozen target to one exact finite-sum identity,
which is proved as `fibreExpansion` in `Expansion.lean`. -/
theorem main_from_residuals (h : Residual_FibreExpansion) :
    AKLT.Blueprint.Rec.RemovedMeanIntervalsStatement := by
  intro a hU f g hN hof hog hfg
  refine ⟨?_, free_response_comparison a.D a.τ a.y a.o f g⟩
  intro b
  obtain ⟨hp, hs⟩ := removed_pair_bounds_from_fibres h a hU f g hN hof hog hfg b
  dsimp only [responseI, responseJ]
  constructor
  · linarith [hs.1]
  · constructor
    · linarith [hs.2]
    · constructor
      · linarith [hp.1]
      · linarith [hp.2]

/-- The frozen target, unconditionally: the fibre residual is proved in `Expansion.lean`. -/
theorem main : AKLT.Blueprint.Rec.RemovedMeanIntervalsStatement :=
  main_from_residuals fibreExpansion

end AKLT.W.REC004
