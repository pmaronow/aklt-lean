import AKLT.Blueprint.Rec.NodesRecursion

noncomputable section
open AKLT.Defs

namespace AKLT.W.REC075

theorem main : AKLT.Blueprint.Rec.ProtectedDistanceFiniteStatement := by
  intro G hG
  obtain ⟨x, hxG, hmax⟩ := Finset.exists_max_image G (fun z : Plane => z.1) hG
  have hout : (x.1 + 1, x.2) ∉ G := by
    intro hy
    have hle := hmax (x.1 + 1, x.2) hy
    omega
  have hboundary : boundaryDepth G x ≤ 1 := by
    unfold boundaryDepth setDistance
    apply (iInf_le_of_le ⟨(x.1 + 1, x.2), hout⟩ ?_)
    simp [latticeDist]
  have hxProtected : x ∈ protectedSites G := by
    simp only [protectedSites, Finset.mem_filter]
    exact ⟨hxG, hboundary.trans (by norm_num)⟩
  refine ⟨⟨x, hxProtected⟩, ?_⟩
  intro z
  have hfinite : setDistance latticeDist z (↑(protectedSites G) : Set Plane) ≤
      (latticeDist z x : ℕ∞) := by
    unfold setDistance
    exact iInf_le_of_le ⟨x, hxProtected⟩ le_rfl
  intro htop
  rw [htop] at hfinite
  simp at hfinite

end AKLT.W.REC075
