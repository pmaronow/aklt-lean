import AKLT.Blueprint.Q.NodesFrames

noncomputable section
open AKLT.Defs

namespace AKLT.W.Q001

private theorem dot_mulVec_preserved (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : R.transpose * R = 1) (u v : Vec3) :
    dot (R.mulVec u) (R.mulVec v) = dot u v := by
  change dotProduct (R.mulVec u) (R.mulVec v) = dotProduct u v
  rw [Matrix.dotProduct_mulVec]
  rw [← Matrix.mulVec_transpose]
  rw [Matrix.mulVec_mulVec, hR]
  simp

theorem main : AKLT.Blueprint.Q.OrthogonalFamilyStatement := by
  intro R hR v hv hunit hanti
  have hRinj : Function.Injective R.mulVec := by
    intro x y hxy
    have h := congrArg (fun z : Vec3 => R.transpose.mulVec z) hxy
    simpa [Matrix.mulVec_mulVec, hR] using h
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    exact hv (hRinj hab)
  · intro a
    rw [normSq, dot_mulVec_preserved R hR]
    exact hunit a
  · intro a
    obtain ⟨b, hb⟩ := hanti a
    refine ⟨b, ?_⟩
    rw [hb, Matrix.mulVec_neg]

end AKLT.W.Q001
