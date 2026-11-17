module
public import AKLT.Blueprint.Win.NodesRemoval

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

open AKLT.Defs
namespace AKLT.W.WIN050

theorem main : AKLT.Blueprint.Win.EnumerationStepsStatement := by
  classical
  intro G X hXG hdepth e
  refine ⟨?_, ?_, ?_⟩
  · ext z
    simp [AKLT.Blueprint.Win.removedPrefix]
  · have hlast : AKLT.Blueprint.Win.removedPrefix e (e.last + 1) =
        Finset.univ.image e.site := by
      ext z
      simp only [AKLT.Blueprint.Win.removedPrefix, Finset.mem_image,
        Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨a, ha, haz⟩
        exact ⟨a, haz⟩
      · rintro ⟨a, haz⟩
        exact ⟨a, by omega, haz⟩
    rw [hlast, e.image_eq]
  · intro j
    have hupdate : AKLT.Blueprint.Win.removedPrefix e (j.val + 1) =
        insert (e.site j) (AKLT.Blueprint.Win.removedPrefix e j.val) := by
      ext z
      simp only [AKLT.Blueprint.Win.removedPrefix, Finset.mem_image,
        Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · rintro ⟨k, hk, hsite⟩
        by_cases hkj : k.val = j.val
        · left
          rw [← hsite]
          congr 1
          exact Fin.ext hkj
        · right
          exact ⟨k, by omega, hsite⟩
      · rintro (hz | ⟨k, hk, hsite⟩)
        · exact ⟨j, by omega, hz.symm⟩
        · exact ⟨k, by omega, hsite⟩
    have hsiteX : e.site j ∈ X := by
      have hmem : e.site j ∈ Finset.univ.image e.site :=
        Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
      rw [e.image_eq] at hmem
      exact hmem
    have hprefixX : AKLT.Blueprint.Win.removedPrefix e j.val ⊆ X := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨k, hk, hky⟩
      have hmem : y ∈ Finset.univ.image e.site :=
        Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hky⟩
      rw [e.image_eq] at hmem
      exact hmem
    have hnotProtected : ∀ x ∈ X, x ∉ protectedSites G := by
      intro x hx hxprotected
      change x ∈ G.filter (fun y => boundaryDepth G y ≤ 2) at hxprotected
      have hle := (Finset.mem_filter.mp hxprotected).2
      have hlt : (2 : ℕ∞) < boundaryDepth G x := by
        exact lt_of_lt_of_le (by norm_num) (hdepth x hx)
      exact (not_le_of_gt hlt) hle
    have hsiteNotPrefix : e.site j ∉ AKLT.Blueprint.Win.removedPrefix e j.val := by
      intro hmem
      rcases Finset.mem_image.mp hmem with ⟨k, hk, hsame⟩
      have hklt : k.val < j.val := (Finset.mem_filter.mp hk).2
      have hkj : k = j := e.injective hsame
      have hval : k.val = j.val := congrArg Fin.val hkj
      omega
    have hstep : AKLT.Blueprint.Win.RemovalStep G
        (AKLT.Blueprint.Win.removedPrefix e j.val) (e.site j) := by
      refine ⟨?_, ?_, hdepth (e.site j) hsiteX⟩
      · intro y hy
        have hyX := hprefixX hy
        exact Finset.mem_sdiff.mpr ⟨hXG hyX, hnotProtected y hyX⟩
      · exact Finset.mem_sdiff.mpr ⟨hXG hsiteX, hsiteNotPrefix⟩
    have hadj : 0 < j.val → ∃ c ∈ AKLT.Blueprint.Win.removedPrefix e j.val,
        Adjacent (e.site j) c := by
      intro hj
      rcases e.previous j hj with ⟨k, hklt, hadj⟩
      refine ⟨e.site k, ?_, hadj⟩
      exact Finset.mem_image.mpr ⟨k,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hklt⟩, rfl⟩
    exact ⟨hupdate, hstep, hadj⟩

end AKLT.W.WIN050

#print axioms AKLT.W.WIN050.main
