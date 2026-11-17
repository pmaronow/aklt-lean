module
public import AKLT.Blueprint.H3.NodesV2Stationary

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.H3M032

theorem main : AKLT.Blueprint.H3.StationaryCentreZeroOperatorStatementV2 := by
  intro m q Q X d₀ F hF φ a x
  simp only [stationaryApplyV2, stationaryApply]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro ψ hψ
  by_cases hdest : x + d.step = kernelCentre
  · have hvalue : F ψ (Q.successor a d) (x + d.step) = 0 := by
      rw [hdest]
      exact hF ψ (Q.successor a d)
    simp [hvalue]
  · have hcoeff :
        stationaryCoefficientV2 Q X d₀ φ a x d ψ =
          stationaryCoefficient Q X d₀ φ a x d ψ := by
      simp [stationaryCoefficientV2, stationaryCoefficient, hdest]
    rw [hcoeff]

end AKLT.W.H3M032
