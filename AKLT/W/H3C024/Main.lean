module
public import CertData.H3.Bridge.Interface

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.H3C024

theorem main : CertData.H3.Bridge.CentreZeroV2Leaf := by
  intro Q C X d₀ hcentre φ a x
  have hsum :
      (∑ d : Compass, ∑ ψ : Phase,
        coefficientCeiling (stationaryCoefficient Q X d₀ φ a x d ψ) *
          C.extended ψ (Q.successor a d) (x + d.step)) =
      ∑ d : Compass, ∑ ψ : Phase,
        coefficientCeiling (stationaryCoefficientV2 Q X d₀ φ a x d ψ) *
          C.extended ψ (Q.successor a d) (x + d.step) := by
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro ψ hψ
    by_cases hdest : x + d.step = kernelCentre
    · have hzero : C.extended ψ (Q.successor a d) (x + d.step) = 0 := by
        rw [hdest]
        exact hcentre ψ (Q.successor a d)
      rw [hzero]
      simp [stationaryCoefficientV2, hdest]
    · have hcoef :
          stationaryCoefficientV2 Q X d₀ φ a x d ψ =
            stationaryCoefficient Q X d₀ φ a x d ψ := by
        simp [stationaryCoefficientV2, stationaryCoefficient, hdest]
      rw [hcoef]
  exact hsum

end AKLT.W.H3C024

#print axioms AKLT.W.H3C024.main
