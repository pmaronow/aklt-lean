import AKLT.Blueprint.Win.NodesTopology

noncomputable section
open AKLT.Defs

namespace AKLT.W.WIN011

private theorem exterior_site_exists (G : Finset Plane) : ∃ z : Plane, z ∉ G := by
  classical
  by_cases hG : G.Nonempty
  · obtain ⟨p, hp, hmax⟩ := G.exists_max_image Prod.fst hG
    refine ⟨(p.1 + 1, p.2), ?_⟩
    intro hmem
    have hle := hmax _ hmem
    simp at hle
  · refine ⟨(0, 0), ?_⟩
    intro hmem
    exact hG ⟨(0, 0), hmem⟩

private theorem boundaryDepth_attained (G : Finset Plane) (x : Plane) :
    ∃ z : Plane, z ∉ G ∧
      boundaryDepth G x = (latticeDist x z : ℕ∞) := by
  classical
  obtain ⟨w, hw⟩ := exterior_site_exists G
  haveI : Nonempty {z : Plane // z ∉ G} := ⟨⟨w, hw⟩⟩
  obtain ⟨z, hz⟩ := ENat.exists_eq_iInf
    (fun z : {z : Plane // z ∉ G} => (latticeDist x z.1 : ℕ∞))
  refine ⟨z.1, z.2, ?_⟩
  change (⨅ y : {z : Plane // z ∉ G}, (latticeDist x y.1 : ℕ∞)) = _
  exact hz.symm

private theorem latticeDist_triangle (x y z : Plane) :
    latticeDist x z ≤ latticeDist x y + latticeDist y z := by
  unfold latticeDist
  have h₁ : (x.1 - z.1).natAbs ≤
      (x.1 - y.1).natAbs + (y.1 - z.1).natAbs := by
    calc
      (x.1 - z.1).natAbs = ((x.1 - y.1) + (y.1 - z.1)).natAbs := by
        congr 1 <;> omega
      _ ≤ (x.1 - y.1).natAbs + (y.1 - z.1).natAbs := Int.natAbs_add_le _ _
  have h₂ : (x.2 - z.2).natAbs ≤
      (x.2 - y.2).natAbs + (y.2 - z.2).natAbs := by
    calc
      (x.2 - z.2).natAbs = ((x.2 - y.2) + (y.2 - z.2)).natAbs := by
        congr 1 <;> omega
      _ ≤ (x.2 - y.2).natAbs + (y.2 - z.2).natAbs := Int.natAbs_add_le _ _
  omega

theorem main : AKLT.Blueprint.Win.FiniteDepthStatement := by
  intro G x
  obtain ⟨z, hz, hdepth⟩ := boundaryDepth_attained G x
  constructor
  · rw [hdepth]
    exact ENat.natCast_ne_top _
  constructor
  · rw [hdepth]
    simp
  constructor
  · constructor
    · intro hzero
      have hdistCast : (latticeDist x z : ℕ∞) = 0 := hdepth.symm.trans hzero
      have hdist : latticeDist x z = 0 := by exact_mod_cast hdistCast
      have hcoords := Nat.add_eq_zero_iff.mp (show
        (x.1 - z.1).natAbs + (x.2 - z.2).natAbs = 0 from hdist)
      have h₁ : x.1 - z.1 = 0 := Int.natAbs_eq_zero.mp hcoords.1
      have h₂ : x.2 - z.2 = 0 := Int.natAbs_eq_zero.mp hcoords.2
      have hEq : x = z := by
        apply Prod.ext
        · exact sub_eq_zero.mp h₁
        · exact sub_eq_zero.mp h₂
      rw [hEq]
      exact hz
    · intro hx
      unfold boundaryDepth setDistance
      apply ENat.iInf_eq_zero.mpr
      refine ⟨⟨x, hx⟩, ?_⟩
      simp [latticeDist]
  · intro y
    obtain ⟨w, hw, hwy⟩ := boundaryDepth_attained G y
    have hle : boundaryDepth G x ≤ (latticeDist x w : ℕ∞) := by
      unfold boundaryDepth setDistance
      change (⨅ q : {z : Plane // z ∉ G}, (latticeDist x q.1 : ℕ∞)) ≤ _
      exact iInf_le _ (⟨w, hw⟩ : {z : Plane // z ∉ G})
    have hleNat := ENat.toNat_le_toNat hle (ENat.natCast_ne_top (latticeDist x w))
    have hyNat : (boundaryDepth G y).toNat = latticeDist y w := by
      rw [hwy]
      simp
    calc
      (boundaryDepth G x).toNat ≤ latticeDist x w := hleNat
      _ ≤ latticeDist x y + latticeDist y w := latticeDist_triangle x y w
      _ = latticeDist x y + (boundaryDepth G y).toNat := by rw [hyNat]

#print axioms main

end AKLT.W.WIN011
