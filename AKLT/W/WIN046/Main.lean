import AKLT.Blueprint.Win.NodesTaper

open AKLT.Defs
open AKLT.Blueprint.Win

namespace AKLT.W.WIN046

private theorem latticeDist_triangle (x z y : Plane) :
    latticeDist x y ≤ latticeDist x z + latticeDist z y := by
  unfold latticeDist
  have h₁ : (x.1 - y.1).natAbs ≤ (x.1 - z.1).natAbs + (z.1 - y.1).natAbs := by
    simpa [sub_add_sub_cancel] using Int.natAbs_add_le (x.1 - z.1) (z.1 - y.1)
  have h₂ : (x.2 - y.2).natAbs ≤ (x.2 - z.2).natAbs + (z.2 - y.2).natAbs := by
    simpa [sub_add_sub_cancel] using Int.natAbs_add_le (x.2 - z.2) (z.2 - y.2)
  omega

private theorem latticeDist_cross_le_one {x z : Plane} (hz : z ∈ cross x) :
    latticeDist x z ≤ 1 := by
  rcases Finset.mem_insert.mp hz with h | hz
  · subst z
    simp [latticeDist]
  · unfold neighbours at hz
    rcases Finset.mem_image.mp hz with ⟨d, _, hdz⟩
    subst z
    cases d <;> simp [latticeDist, Compass.step]

private theorem deep_cross_site (G : Finset Plane) (x z : Plane)
    (hz : z ∈ cross x) (hdepth : 14 ≤ boundaryDepth G x) :
    z ∈ G ∧ 13 ≤ boundaryDepth G z := by
  have hstep : latticeDist x z ≤ 1 := latticeDist_cross_le_one hz
  have hmem : z ∈ G := by
    by_contra hout
    have hbound : boundaryDepth G x ≤ (latticeDist x z : ℕ∞) := by
      unfold boundaryDepth setDistance
      exact iInf_le _ (⟨z, hout⟩ : {w : Plane // w ∉ G})
    have hcontra : (14 : ℕ∞) ≤ (1 : ℕ∞) :=
      le_trans hdepth (le_trans hbound (by exact_mod_cast hstep))
    norm_num at hcontra
  have hdepthz : 13 ≤ boundaryDepth G z := by
    change (13 : ℕ∞) ≤ ⨅ y : {w : Plane // w ∉ G}, (latticeDist z y.val : ℕ∞)
    apply le_iInf
    intro y
    have hbound : boundaryDepth G x ≤ (latticeDist x y.val : ℕ∞) := by
      unfold boundaryDepth setDistance
      exact iInf_le _ y
    have hnat : 14 ≤ latticeDist x y.val := by
      exact_mod_cast (le_trans hdepth hbound)
    have htri := latticeDist_triangle x z y.val
    have hnat' : 13 ≤ latticeDist z y.val := by omega
    exact_mod_cast hnat'
  exact ⟨hmem, hdepthz⟩

theorem main : AKLT.Blueprint.Win.ThickDepthStatement := by
  intro G X₀ hdeep
  constructor
  · intro z hz
    unfold thicken at hz
    rcases Finset.mem_biUnion.mp hz with ⟨x, hx, hz⟩
    exact (deep_cross_site G x z hz (hdeep x hx)).1
  · intro z hz
    unfold thicken at hz
    rcases Finset.mem_biUnion.mp hz with ⟨x, hx, hz⟩
    exact (deep_cross_site G x z hz (hdeep x hx)).2

end AKLT.W.WIN046

#print axioms AKLT.W.WIN046.main
