module
public import AKLT.Blueprint.H3.NodesV2Stationary

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.H3M034

theorem main : AKLT.Blueprint.H3.StationaryCertificateBridgeStatementV2 := by
  intro m q Q X d₀ C hpass
  rcases hpass with ⟨hpos, hcaps, hfree, hvalue, hterminal, hrows⟩
  refine ⟨hpos, hcaps, hfree, hvalue, hterminal, ?_⟩
  intro φ a x hxCenter hxTarget
  have hsum :
      (∑ d : Compass, ∑ ψ : Phase,
        coefficientCeiling (stationaryCoefficient Q X d₀ φ a x.val d ψ) *
          C.extended ψ (Q.successor a d) (x.val + d.step)) =
      (∑ d : Compass, ∑ ψ : Phase,
        coefficientCeiling (stationaryCoefficientV2 Q X d₀ φ a x.val d ψ) *
          C.extended ψ (Q.successor a d) (x.val + d.step)) := by
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro ψ hψ
    by_cases hdest : x.val + d.step = kernelCenter
    · have hzero : C.extended ψ (Q.successor a d) (x.val + d.step) = 0 := by
        rw [hdest]
        exact (hterminal ψ (Q.successor a d)).1
      rw [hzero]
      simp [stationaryCoefficientV2, hdest]
    · have hcoef :
          stationaryCoefficientV2 Q X d₀ φ a x.val d ψ =
            stationaryCoefficient Q X d₀ φ a x.val d ψ := by
        simp [stationaryCoefficientV2, stationaryCoefficient, hdest]
      rw [hcoef]
  rw [hsum]
  exact hrows φ a x hxCenter hxTarget

end AKLT.W.H3M034
