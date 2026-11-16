import AKLT.Blueprint.Win.NodesCut

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.WIN065

theorem main : AKLT.Blueprint.Win.MarginalNormalizationStatement := by
  classical
  intro κ F B hBF η hZ
  have hden :
      (∑ s : PlaneConfiguration B, AKLT.Blueprint.Win.marginalNumerator κ F B η s) =
        ∑ σ : PlaneConfiguration F, planeWeight κ F η σ := by
    unfold AKLT.Blueprint.Win.marginalNumerator
    rw [Finset.sum_comm]
    simp
  funext s
  simp only [AKLT.Defs.planeMarginal, AKLT.Defs.marginal, AKLT.Defs.planeLaw,
    AKLT.Defs.normalize]
  rw [hden]
  unfold AKLT.Blueprint.Win.marginalNumerator
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro σ hσ
  by_cases hp : (fun z : B => extendLetters σ z.val) = s <;> simp [hp]

end AKLT.W.WIN065
