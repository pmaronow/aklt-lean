module
public import AKLT.Blueprint.Rec.NodesV2Local

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open AKLT.Defs
open AKLT.Blueprint.Rec

namespace AKLT.W.REC093

private theorem adjacent_positiveNeighbors (x y : Plane) (h : Adjacent x y) :
    y ∈ positiveNeighbors x ∨ x ∈ positiveNeighbors y := by
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  simp [Adjacent, latticeDist, positiveNeighbors] at h ⊢
  omega

private theorem positiveNeighbors_adjacent (x y : Plane)
    (h : y ∈ positiveNeighbors x) : Adjacent x y := by
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  simp [positiveNeighbors] at h
  rcases h with h | h
  · rcases h with ⟨h₁, h₂⟩
    subst y₁
    subst y₂
    simp [Adjacent, latticeDist]
  · rcases h with ⟨h₁, h₂⟩
    subst y₁
    subst y₂
    simp [Adjacent, latticeDist]

private theorem internalBond_adjacent (G : Finset Plane) {x y : Plane}
    (h : (x, y) ∈ internalBonds G) : Adjacent x y := by
  rw [internalBonds, Finset.mem_biUnion] at h
  rcases h with ⟨a, ha, h⟩
  rw [Finset.mem_image] at h
  rcases h with ⟨b, hb, hab⟩
  rcases Finset.mem_inter.mp hb with ⟨hb, _⟩
  have hab' : a = x ∧ b = y := by
    cases a
    cases b
    simp_all
  rcases hab' with ⟨rfl, rfl⟩
  exact positiveNeighbors_adjacent _ _ hb

private theorem adjacent_internalBond (G : Finset Plane) {x y : Plane}
    (hx : x ∈ G) (hy : y ∈ G) (h : Adjacent x y) :
    (x, y) ∈ internalBonds G ∨ (y, x) ∈ internalBonds G := by
  rcases adjacent_positiveNeighbors x y h with hxy | hyx
  · left
    rw [internalBonds, Finset.mem_biUnion]
    exact ⟨x, hx, Finset.mem_image.mpr ⟨y, Finset.mem_inter.mpr ⟨hxy, hy⟩, rfl⟩⟩
  · right
    rw [internalBonds, Finset.mem_biUnion]
    exact ⟨y, hy, Finset.mem_image.mpr ⟨x, Finset.mem_inter.mpr ⟨hyx, hx⟩, rfl⟩⟩

private theorem adjacent_symm {x y : Plane} (h : Adjacent x y) : Adjacent y x := by
  have hsub : ∀ a b : ℤ, (a - b).natAbs = (b - a).natAbs := by
    intro a b
    calc
      (a - b).natAbs = (-(a - b)).natAbs := (Int.natAbs_neg _).symm
      _ = (b - a).natAbs := by rw [neg_sub]
  simpa only [Adjacent, latticeDist, hsub x.1 y.1, hsub x.2 y.2] using h

private theorem eastChart_adjacent (x y : Plane) :
    Adjacent ((0, 0) + normalizeRotation .east x)
      ((0, 0) + normalizeRotation .east y) ↔ Adjacent x y := by
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  have hsub : ∀ a b : ℤ, (a - b).natAbs = (b - a).natAbs := by
    intro a b
    calc
      (a - b).natAbs = (-(a - b)).natAbs := (Int.natAbs_neg _).symm
      _ = (b - a).natAbs := by rw [neg_sub]
  simp [Adjacent, latticeDist, normalizeRotation]
  rw [show -x₁ + y₁ = y₁ - x₁ by omega, hsub y₁ x₁]
  omega

theorem main : AKLT.Blueprint.Rec.BoundaryExampleCoveredStatementV2 := by
  let D : Network boundaryExampleG := normalizeStart boundaryExampleD (0, 0) (-1, 0)
  let chart : Plane → Plane := fun z => (0, 0) + normalizeRotation .east z
  change AKLT.Defs.CoveredDepartureV2 D (0, 0) .east .east
  have hOld : AKLT.Blueprint.Rec.CoveredDepartureV2 D (0, 0) .east .east := by
    change AKLT.Blueprint.Rec.CoveredDepartureV2
      (normalizeStart boundaryExampleD (0, 0) (-1, 0)) (0, 0) .east .east
    refine ⟨boundaryExamplePattern, ?_, rfl, ?_⟩
    · unfold PatternData.Covered
      repeat' apply And.intro
      all_goals decide +kernel
    · decide +kernel
  obtain ⟨π, hπ, hrot, hmatch⟩ := hOld
  have chart_injective : Function.Injective chart := by
    intro a b hab
    dsimp [chart, normalizeRotation] at hab
    rcases a with ⟨a₁, a₂⟩
    rcases b with ⟨b₁, b₂⟩
    simp at hab
    rcases hab with ⟨h₂, h₁⟩
    apply Prod.ext <;> omega
  have hkeep_iff (x y : Plane) (hx : x ∈ templateSites \ templateTips)
      (hyG : chart y ∈ boundaryExampleG) (hxn : π.statusAt x ≠ .X) :
      y ∈ π.keptAt x ↔ chart y ∈ D.kept (chart x) := by
    have hData := (hmatch x hx).2 hxn
    rw [← hData]
    constructor
    · intro hy
      apply Finset.mem_inter.mpr
      exact ⟨Finset.mem_image.mpr ⟨y, hy, rfl⟩, hyG⟩
    · intro hy
      rcases Finset.mem_inter.mp hy with ⟨hyImage, _⟩
      rcases Finset.mem_image.mp hyImage with ⟨y', hy', heq⟩
      have hyEq : y' = y := chart_injective heq
      simpa [hyEq] using hy'
  have status_mem_G (x : Plane) (hx : D.status x ≠ .X) :
      x ∈ boundaryExampleG := by
    by_contra hnot
    have hX : D.status x = .X := by
      simp [D, normalizeStart, boundaryExampleD, hnot]
    exact hx hX
  have active_of_status (x : Plane) (hx : D.status x ≠ .X) : x ∈ D.active :=
    Finset.mem_filter.mpr ⟨status_mem_G x hx, hx⟩
  have extract (x y : Plane) (hxy : (x, y) ∈ π.bonds) :
      (x, y) ∈ internalBonds templateSites ∧
      π.statusAt x ≠ .X ∧ π.statusAt y ≠ .X ∧
      (x ∈ templateTips ∨ y ∈ π.keptAt x) ∧
      (y ∈ templateTips ∨ x ∈ π.keptAt y) := by
    unfold PatternData.bonds at hxy
    exact Finset.mem_filter.mp hxy
  refine ⟨π, hπ, hrot, ?_, ?_⟩
  · intro z hz
    exact (hmatch z hz).1
  · intro z hz t ht
    by_cases htip : t ∈ templateTips
    · simp [htip]
      intro hPresent
      rcases hPresent with ⟨hzActive, htActive, hAdj, hKeepZ, _⟩
      have hzN : D.status (chart z) ≠ .X := (Finset.mem_filter.mp hzActive).2
      have hπzN : π.statusAt z ≠ .X := by rw [(hmatch z hz).1]; exact hzN
      have hπtN : π.statusAt t ≠ .X := by
        rcases hπ with ⟨_, _, _, _, _, _, _, _, htipU, _⟩
        rw [htipU t htip]
        decide
      have hKeep : t ∈ π.keptAt z :=
        (hkeep_iff z t hz (Finset.mem_filter.mp htActive).1 hπzN).2 hKeepZ
      have hAdj' : Adjacent z t := (eastChart_adjacent z t).mp hAdj
      rcases adjacent_internalBond templateSites (Finset.mem_sdiff.mp hz).1 ht hAdj' with hzt | htz
      · apply Or.inl
        unfold PatternData.bonds
        apply Finset.mem_filter.mpr
        exact ⟨hzt, ⟨hπzN, hπtN, Or.inr hKeep, Or.inl htip⟩⟩
      · apply Or.inr
        unfold PatternData.bonds
        apply Finset.mem_filter.mpr
        exact ⟨htz, ⟨hπtN, hπzN, Or.inl htip, Or.inr hKeep⟩⟩
    · simp [htip]
      have ht' : t ∈ templateSites \ templateTips := Finset.mem_sdiff.mpr ⟨ht, htip⟩
      have hstatusZ := (hmatch z hz).1
      have hstatusT := (hmatch t ht').1
      constructor
      · intro hInternal
        rcases hInternal with hzt | htz
        · obtain ⟨hbase, hπzN, hπtN, hcondZ, hcondT⟩ := extract z t hzt
          have hkeepZ : t ∈ π.keptAt z := by
            rcases hcondZ with hbad | hkeepZ
            · exact False.elim ((Finset.mem_sdiff.mp hz).2 hbad)
            · exact hkeepZ
          have hkeepT : z ∈ π.keptAt t := by
            rcases hcondT with hbad | hkeepT
            · exact False.elim (htip hbad)
            · exact hkeepT
          have hstatusZ' : D.status (chart z) ≠ .X := by rw [← hstatusZ]; exact hπzN
          have hstatusT' : D.status (chart t) ≠ .X := by rw [← hstatusT]; exact hπtN
          have hzActive := active_of_status (chart z) hstatusZ'
          have htActive := active_of_status (chart t) hstatusT'
          refine ⟨hzActive, htActive, ?_, ?_, ?_⟩
          · exact (eastChart_adjacent z t).mpr (internalBond_adjacent templateSites hbase)
          · exact (hkeep_iff z t hz (status_mem_G (chart t) hstatusT') hπzN).1 hkeepZ
          · exact (hkeep_iff t z ht' (status_mem_G (chart z) hstatusZ') hπtN).1 hkeepT
        · obtain ⟨hbase, hπtN, hπzN, hcondT, hcondZ⟩ := extract t z htz
          have hkeepT : z ∈ π.keptAt t := by
            rcases hcondT with hbad | hkeepT
            · exact False.elim (htip hbad)
            · exact hkeepT
          have hkeepZ : t ∈ π.keptAt z := by
            rcases hcondZ with hbad | hkeepZ
            · exact False.elim ((Finset.mem_sdiff.mp hz).2 hbad)
            · exact hkeepZ
          have hstatusZ' : D.status (chart z) ≠ .X := by rw [← hstatusZ]; exact hπzN
          have hstatusT' : D.status (chart t) ≠ .X := by rw [← hstatusT]; exact hπtN
          have hzActive := active_of_status (chart z) hstatusZ'
          have htActive := active_of_status (chart t) hstatusT'
          refine ⟨hzActive, htActive, ?_, ?_, ?_⟩
          · exact (eastChart_adjacent z t).mpr
              (adjacent_symm (internalBond_adjacent templateSites hbase))
          · exact (hkeep_iff z t hz (status_mem_G (chart t) hstatusT') hπzN).1 hkeepZ
          · exact (hkeep_iff t z ht' (status_mem_G (chart z) hstatusZ') hπtN).1 hkeepT
      · intro hPresent
        rcases hPresent with ⟨hzActive, htActive, hAdj, hKeepZ, hKeepT⟩
        have hzN : D.status (chart z) ≠ .X := (Finset.mem_filter.mp hzActive).2
        have htN : D.status (chart t) ≠ .X := (Finset.mem_filter.mp htActive).2
        have hπzN : π.statusAt z ≠ .X := by rw [hstatusZ]; exact hzN
        have hπtN : π.statusAt t ≠ .X := by rw [hstatusT]; exact htN
        have hKeepZ' : t ∈ π.keptAt z :=
          (hkeep_iff z t hz (Finset.mem_filter.mp htActive).1 hπzN).2 hKeepZ
        have hKeepT' : z ∈ π.keptAt t :=
          (hkeep_iff t z ht' (Finset.mem_filter.mp hzActive).1 hπtN).2 hKeepT
        have hAdj' : Adjacent z t := (eastChart_adjacent z t).mp hAdj
        rcases adjacent_internalBond templateSites (Finset.mem_sdiff.mp hz).1 ht hAdj' with hzt | htz
        · apply Or.inl
          unfold PatternData.bonds
          apply Finset.mem_filter.mpr
          exact ⟨hzt, ⟨hπzN, hπtN, Or.inr hKeepZ', Or.inr hKeepT'⟩⟩
        · apply Or.inr
          unfold PatternData.bonds
          apply Finset.mem_filter.mpr
          exact ⟨htz, ⟨hπtN, hπzN, Or.inr hKeepT', Or.inr hKeepZ'⟩⟩

end AKLT.W.REC093
