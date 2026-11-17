import AKLT.Blueprint.Mom.NodesMean

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.MOM029

theorem main : AKLT.Blueprint.Mom.OrthogonalNormStatement := by
  intro R hR v
  change (R.mulVec v) ⬝ᵥ (R.mulVec v) = v ⬝ᵥ v
  rw [← Matrix.dotProduct_transpose_mulVec (A := R) (x := v) (y := R.mulVec v)]
  rw [Matrix.mulVec_mulVec]
  rw [hR, Matrix.one_mulVec]

end AKLT.W.MOM029
