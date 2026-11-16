import AKLT.Blueprint.H1.NodesLeaf

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs

namespace AKLT.W.H1M002

private theorem dot_swap (a b : Vec3) : dot a b = dot b a := by
  unfold dot
  apply Finset.sum_congr rfl
  intro i hi
  ring

private def slots2 (m : Fin 20 → UnitVector) (i : Fin 18) : Fin 2 → UnitVector :=
  fun j => m ⟨i.val + j.val, by omega⟩

private def slots3 (m : Fin 20 → UnitVector) (i : Fin 18) : Fin 3 → UnitVector :=
  fun j => m ⟨i.val + j.val, by omega⟩

private lemma fieldCorner00 (m : Fin 20 → UnitVector) :
    coveredSiteField m (1, 1) = localProduct (fun j => (slots2 m ⟨0, by omega⟩ j).val) := by
  unfold coveredSiteField localProduct
  funext n
  simp only [Fin.prod_univ_succ]
  simp [externalSlot, slots2, dot_swap]

private lemma fieldCorner10 (m : Fin 20 → UnitVector) :
    coveredSiteField m (-1, 1) = localProduct (fun j => (slots2 m ⟨2, by omega⟩ j).val) := by
  unfold coveredSiteField localProduct
  funext n
  simp only [Fin.prod_univ_succ]
  simp [externalSlot, slots2, dot_swap]

private lemma fieldCorner11 (m : Fin 20 → UnitVector) :
    coveredSiteField m (-1, -1) = localProduct (fun j => (slots2 m ⟨4, by omega⟩ j).val) := by
  unfold coveredSiteField localProduct
  funext n
  simp only [Fin.prod_univ_succ]
  simp [externalSlot, slots2, dot_swap]

private lemma fieldCorner01 (m : Fin 20 → UnitVector) :
    coveredSiteField m (1, -1) = localProduct (fun j => (slots2 m ⟨6, by omega⟩ j).val) := by
  unfold coveredSiteField localProduct
  funext n
  simp only [Fin.prod_univ_succ]
  simp [externalSlot, slots2, dot_swap]

private lemma fieldTipEast (m : Fin 20 → UnitVector) :
    coveredSiteField m (2, 0) = localProduct (fun j => (slots3 m ⟨8, by omega⟩ j).val) := by
  unfold coveredSiteField localProduct
  funext n
  simp only [Fin.prod_univ_succ]
  simp [externalSlot, slots3, dot_swap]

private lemma fieldTipNorth (m : Fin 20 → UnitVector) :
    coveredSiteField m (0, 2) = localProduct (fun j => (slots3 m ⟨11, by omega⟩ j).val) := by
  unfold coveredSiteField localProduct
  funext n
  simp only [Fin.prod_univ_succ]
  simp [externalSlot, slots3, dot_swap]

private lemma fieldTipWest (m : Fin 20 → UnitVector) :
    coveredSiteField m (-2, 0) = localProduct (fun j => (slots3 m ⟨14, by omega⟩ j).val) := by
  unfold coveredSiteField localProduct
  funext n
  simp only [Fin.prod_univ_succ]
  simp [externalSlot, slots3, dot_swap]

private lemma fieldTipSouth (m : Fin 20 → UnitVector) :
    coveredSiteField m (0, -2) = localProduct (fun j => (slots3 m ⟨17, by omega⟩ j).val) := by
  unfold coveredSiteField localProduct
  funext n
  simp only [Fin.prod_univ_succ]
  simp [externalSlot, slots3, dot_swap]

theorem main : AKLT.Blueprint.H1.CoveredSlotEnumerationStatement := by
  intro π hCovered m x hx hnotX
  have hxper : x ∈ templateCorners ∨ x ∈ templateTips := Finset.mem_union.mp hx
  rcases hCovered with ⟨_, _, _, _, _, _, hCorners, _, hTips, _⟩
  rcases hxper with hxCorner | hxTip
  · simp [templateCorners] at hxCorner
    rcases hxCorner with rfl | rfl | rfl | rfl
    · have hstat : π.statusAt (1, 1) = .U ∨ π.statusAt (1, 1) = .D := by
        rcases hCorners (1, 1) (by simp [templateCorners]) with hu | hx | hd
        · exact Or.inl hu
        · exact False.elim (hnotX hx)
        · exact Or.inr hd.1
      refine Or.inr ⟨slots2 m ⟨0, by omega⟩, hstat, ?_, fieldCorner00 m⟩
      rcases hstat with hu | hd
      · simp [replacementRadius, templateTips, hu]
      · simp [replacementRadius, templateTips, hd]
    · have hstat : π.statusAt (-1, 1) = .U ∨ π.statusAt (-1, 1) = .D := by
        rcases hCorners (-1, 1) (by simp [templateCorners]) with hu | hx | hd
        · exact Or.inl hu
        · exact False.elim (hnotX hx)
        · exact Or.inr hd.1
      refine Or.inr ⟨slots2 m ⟨2, by omega⟩, hstat, ?_, fieldCorner10 m⟩
      rcases hstat with hu | hd
      · simp [replacementRadius, templateTips, hu]
      · simp [replacementRadius, templateTips, hd]
    · have hstat : π.statusAt (-1, -1) = .U ∨ π.statusAt (-1, -1) = .D := by
        rcases hCorners (-1, -1) (by simp [templateCorners]) with hu | hx | hd
        · exact Or.inl hu
        · exact False.elim (hnotX hx)
        · exact Or.inr hd.1
      refine Or.inr ⟨slots2 m ⟨4, by omega⟩, hstat, ?_, fieldCorner11 m⟩
      rcases hstat with hu | hd
      · simp [replacementRadius, templateTips, hu]
      · simp [replacementRadius, templateTips, hd]
    · have hstat : π.statusAt (1, -1) = .U ∨ π.statusAt (1, -1) = .D := by
        rcases hCorners (1, -1) (by simp [templateCorners]) with hu | hx | hd
        · exact Or.inl hu
        · exact False.elim (hnotX hx)
        · exact Or.inr hd.1
      refine Or.inr ⟨slots2 m ⟨6, by omega⟩, hstat, ?_, fieldCorner01 m⟩
      rcases hstat with hu | hd
      · simp [replacementRadius, templateTips, hu]
      · simp [replacementRadius, templateTips, hd]
  · simp [templateTips] at hxTip
    rcases hxTip with rfl | rfl | rfl | rfl
    · have hs : π.statusAt (2, 0) = .U := hTips (2, 0) (by simp [templateTips])
      refine Or.inl ⟨slots3 m ⟨8, by omega⟩, hs, ?_, fieldTipEast m⟩
      simp [replacementRadius, templateTips]
    · have hs : π.statusAt (0, 2) = .U := hTips (0, 2) (by simp [templateTips])
      refine Or.inl ⟨slots3 m ⟨11, by omega⟩, hs, ?_, fieldTipNorth m⟩
      simp [replacementRadius, templateTips]
    · have hs : π.statusAt (-2, 0) = .U := hTips (-2, 0) (by simp [templateTips])
      refine Or.inl ⟨slots3 m ⟨14, by omega⟩, hs, ?_, fieldTipWest m⟩
      simp [replacementRadius, templateTips]
    · have hs : π.statusAt (0, -2) = .U := hTips (0, -2) (by simp [templateTips])
      refine Or.inl ⟨slots3 m ⟨17, by omega⟩, hs, ?_, fieldTipSouth m⟩
      simp [replacementRadius, templateTips]

end AKLT.W.H1M002

end
