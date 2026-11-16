import AKLT.Blueprint.Rec.Definitions

noncomputable section
open AKLT.Defs

namespace AKLT.Blueprint.Rec

/-- A translated taxicab ball. The passage (0,0) has depth three, its
removed centre (-1,0) depth four, and corner (1,1) lies on the boundary. -/
def boundaryExampleG : Finset Plane :=
  (square (-2, 0) 4).filter fun x => latticeDist x (-2, 0) ≤ 4

/-- The ordinary U/X removal domain underlying the example; the normalized
version only erases the passage flag to the removed centre. -/
def boundaryExampleD : Network boundaryExampleG where
  status := fun x => if x ∈ boundaryExampleG ∧ x ≠ (-1, 0) then .U else .X
  kept := fun x => neighbours x ∩ boundaryExampleG

/-- The covering pattern for the same straight departure. Tips are covering U
and both corner slots are retained. -/
def boundaryExamplePattern : PatternData where
  outgoing := .north
  status := fun z => if z.val = (0, -1) then .X else .U
  kept := fun z => if z.val = (0, 0) then {.east, .north, .west} else Finset.univ

/-- V2 accepts the concrete boundary configuration rejected by the old matcher. -/
theorem boundaryExample_v2_covered :
    CoveredDepartureV2 (normalizeStart boundaryExampleD (0, 0) (-1, 0))
      (0, 0) .east .east := by
  refine ⟨boundaryExamplePattern, ?_, rfl, ?_⟩
  · unfold PatternData.Covered
    repeat' apply And.intro
    all_goals decide +kernel
  · decide +kernel

/-- The old matcher rejects an actual full-kept U boundary corner, even
though its outside directions are original legs. This is the precise
obstruction to using that matcher in the closure lemma. -/
theorem boundaryExample_not_old_covered :
    ¬ CoveredDeparture (normalizeStart boundaryExampleD (0, 0) (-1, 0))
      (0, 0) .east .east := by
  intro h
  obtain ⟨π, hπ, _, hm⟩ := h
  have hz : (-1, 1) ∈ templateSites \ templateTips := by
    norm_num [templateSites, templateTips, square, latticeDist]
  obtain ⟨hstatus, hkept⟩ := hm (-1, 1) hz
  have hU : π.statusAt (-1, 1) = .U := by
    simpa [normalizeStart, boundaryExampleD, boundaryExampleG, normalizeRotation,
      square, latticeDist] using hstatus
  rcases hπ with ⟨_, _, _, _, _, _, _, hfull, _, _⟩
  have hfull' : π.keptAt (-1, 1) = neighbours (-1, 1) :=
    hfull _ (Finset.mem_sdiff.mp hz).1 (by decide) (Finset.mem_sdiff.mp hz).2 hU
  have ht : (-1, 2) ∈ π.keptAt (-1, 1) := by
    rw [hfull']
    exact Finset.mem_image.mpr ⟨Compass.north, Finset.mem_univ _, rfl⟩
  have hmem := Finset.mem_image.mpr
    (⟨(-1, 2), ht, rfl⟩ : ∃ x ∈ π.keptAt (-1, 1),
      (0, 0) + normalizeRotation .east x = (2, 1))
  rw [hkept (by simp [hU])] at hmem
  norm_num [normalizeStart, boundaryExampleD, boundaryExampleG, normalizeRotation,
    square, latticeDist] at hmem

end AKLT.Blueprint.Rec
