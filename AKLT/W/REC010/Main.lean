import AKLT.Blueprint.Rec.NodesResponse
import AKLT.W.REC010.Positive

noncomputable section
open scoped BigOperators
open AKLT.Defs
open AKLT.Blueprint.Rec

namespace AKLT.W.REC010

/-- The one-step trace preserves the auxiliary local rules at an admissible start. -/
theorem traceStep_auxiliary {G : Finset Plane} {D : Network G}
    (hD : D.Auxiliary) {y o : Plane}
    (hy : D.AdmissibleStart y) (ho : o ∈ D.presentNeighbours y) :
    (traceStep D y o).Auxiliary := by
  classical
  rcases hD with ⟨hlocal, hprotected⟩
  rcases hlocal with ⟨hout, hkept, hDdegree, hdegree⟩
  rcases hy with ⟨hyactive, hyoutside, hycase⟩
  have hyo : D.Present y o := (Finset.mem_filter.mp ho).2
  have hyoActive : y ∈ D.active := hyo.1
  have hyG : y ∈ G := (Finset.mem_filter.mp hyoActive).1
  have hactiveSub : (traceStep D y o).active ⊆ D.active := by
    intro x hx
    simp only [Network.active, Finset.mem_filter] at hx ⊢
    rcases hx with ⟨hxG, hxstatus⟩
    refine ⟨hxG, ?_⟩
    by_cases hxy : x = y
    · subst x
      cases hs : D.status y <;> simp [traceStep, hs] at hxstatus ⊢
    · simpa [traceStep, hxy] using hxstatus
  have hkeptSub (x : Plane) : (traceStep D y o).kept x ⊆ D.kept x := by
    change (if x = y then (D.kept x).erase o
      else if x = o then (D.kept x).erase y else D.kept x) ⊆ D.kept x
    intro z hz
    by_cases hxy : x = y
    · subst x
      simp only at hz
      exact (Finset.mem_erase.mp hz).2
    · by_cases hxo : x = o
      · subst x
        simp [hxy] at hz
        exact hz.2
      · simpa [hxy, hxo] using hz
  have hpresentSub (x z : Plane) :
      (traceStep D y o).Present x z → D.Present x z := by
    intro hp
    rcases hp with ⟨hx, hz, hadj, hzx, hxz⟩
    exact ⟨hactiveSub hx, hactiveSub hz, hadj,
      hkeptSub x hzx, hkeptSub z hxz⟩
  have hneighSub (x : Plane) :
      (traceStep D y o).presentNeighbours x ⊆ D.presentNeighbours x := by
    intro z hz
    simp only [Network.presentNeighbours, Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, hpresentSub x z hz.2⟩
  have hneighYErase : (traceStep D y o).presentNeighbours y ⊆
      (D.presentNeighbours y).erase o := by
    intro z hz
    have hzOld := hneighSub y hz
    have hzNe : z ≠ o := by
      intro hzo
      subst z
      have hpres := (Finset.mem_filter.mp hz).2
      rcases hpres with ⟨_, _, _, hkeep, _⟩
      simp [traceStep] at hkeep
    exact Finset.mem_erase.mpr ⟨hzNe, hzOld⟩
  have hneighYCard : ((traceStep D y o).presentNeighbours y).card ≤
      (D.presentNeighbours y).card := Finset.card_le_card (hneighSub y)
  have hstatusNe (x : Plane) (hx : x ≠ y) :
      (traceStep D y o).status x = D.status x := by simp [traceStep, hx]
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hxG
      have hxy : x ≠ y := by
        intro h
        subst x
        exact hxG hyG
      rw [hstatusNe x hxy]
      exact hout x hxG
    · intro x z hz
      exact hkept x (hkeptSub x hz)
    · intro x hxG hs
      by_cases hxy : x = y
      · subst x
        have hCard : (D.presentNeighbours y).card ≤ 3 := by
          rcases hycase with hU | hDcase
          · exact hU.2
          · simp [traceStep, hDcase.1] at hs
        have hNewCard : ((traceStep D y o).presentNeighbours y).card ≤ 2 := by
          have hEraseCard : ((D.presentNeighbours y).erase o).card =
              (D.presentNeighbours y).card - 1 := Finset.card_erase_of_mem ho
          calc
            _ ≤ ((D.presentNeighbours y).erase o).card := Finset.card_le_card hneighYErase
            _ ≤ 2 := by rw [hEraseCard]; omega
        exact hNewCard
      · rw [hstatusNe x hxy] at hs
        have hcard : ((traceStep D y o).presentNeighbours x).card ≤
            (D.presentNeighbours x).card := Finset.card_le_card (hneighSub x)
        exact hcard.trans (hDdegree x hxG hs)
    · intro x hxActive
      have hxOld : x ∈ D.active := hactiveSub hxActive
      by_cases hxy : x = y
      · subst x
        have hbound := hdegree y hyoActive
        have hcard := hneighYCard
        omega
      ·
        have hcard := Finset.card_le_card (hneighSub x)
        have hbound := hdegree x hxOld
        omega
  · intro x hxP
    have hxy : x ≠ y := by
      intro h
      subst x
      exact hyoutside hxP
    rw [hstatusNe x hxy]
    exact hprotected x hxP

/-- Both normalizers of an admissible one-step trace are strictly positive. -/
theorem main : AKLT.Blueprint.Rec.StepRatioPositiveStatement := by
  intro a b
  have hden := partition_pos a.D a.τ a.auxiliary b
  have htrace := traceStep_auxiliary a.auxiliary a.start a.present
  have hnum : 0 < (traceNetwork a.D [a.y, a.o]).partition a.τ b (fun _ => 1) := by
    simpa [traceNetwork] using partition_pos (traceStep a.D a.y a.o) a.τ htrace b
  unfold AKLT.Defs.stepRatio AKLT.Defs.traceRatio
  exact div_pos hnum hden

end AKLT.W.REC010
