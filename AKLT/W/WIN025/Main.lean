import AKLT.Blueprint.Win.NodesTopology

noncomputable section
open AKLT.Defs
open AKLT.Blueprint.Win

namespace AKLT.W.WIN025

theorem main : AKLT.Blueprint.Win.CrossFactsStatement := by
  intro x
  have hstep_inj : Function.Injective (fun d : Compass => x + d.step) := by
    intro d e h
    cases d <;> cases e <;> simp [Compass.step] at h ⊢
  have hx_not_neigh : x ∉ neighbours x := by
    intro h
    unfold neighbours at h
    rcases Finset.mem_image.mp h with ⟨d, hd, hdeq⟩
    cases d <;> simp [Compass.step] at hdeq
  have hneigh_card : (neighbours x).card = 4 := by
    unfold neighbours
    rw [Finset.card_image_of_injective _ hstep_inj]
    decide
  have hcard : (cross x).card = 5 := by
    simp [cross, hx_not_neigh, hneigh_card]
  have hcross_list : ∀ z : Plane,
      z ∈ cross x ↔ z = x ∨ z = x + Compass.east.step ∨
        z = x + Compass.north.step ∨ z = x + Compass.west.step ∨
        z = x + Compass.south.step := by
    intro z
    constructor
    · intro hz
      simp only [cross, Finset.mem_insert] at hz
      rcases hz with hzx | hz
      · exact Or.inl hzx
      · right
        unfold neighbours at hz
        rcases Finset.mem_image.mp hz with ⟨d, hd, hdz⟩
        cases d with
        | east => exact Or.inl hdz.symm
        | north => exact Or.inr (Or.inl hdz.symm)
        | west => exact Or.inr (Or.inr (Or.inl hdz.symm))
        | south => exact Or.inr (Or.inr (Or.inr hdz.symm))
    · intro hz
      rcases hz with hzx | he | hn | hw | hs
      · simp [cross, hzx]
      · simp only [cross, Finset.mem_insert]
        right
        change z ∈ Finset.univ.image (fun d : Compass => x + d.step)
        apply Finset.mem_image.mpr
        exact ⟨Compass.east, Finset.mem_univ _, by simpa [Compass.step] using he.symm⟩
      · simp only [cross, Finset.mem_insert]
        right
        change z ∈ Finset.univ.image (fun d : Compass => x + d.step)
        apply Finset.mem_image.mpr
        exact ⟨Compass.north, Finset.mem_univ _, by simpa [Compass.step] using hn.symm⟩
      · simp only [cross, Finset.mem_insert]
        right
        change z ∈ Finset.univ.image (fun d : Compass => x + d.step)
        apply Finset.mem_image.mpr
        exact ⟨Compass.west, Finset.mem_univ _, by simpa [Compass.step] using hw.symm⟩
      · simp only [cross, Finset.mem_insert]
        right
        change z ∈ Finset.univ.image (fun d : Compass => x + d.step)
        apply Finset.mem_image.mpr
        exact ⟨Compass.south, Finset.mem_univ _, by simpa [Compass.step] using hs.symm⟩
  have hdist_list : ∀ z : Plane,
      latticeDist z x ≤ 1 ↔ z = x ∨ z = x + Compass.east.step ∨
        z = x + Compass.north.step ∨ z = x + Compass.west.step ∨
        z = x + Compass.south.step := by
    intro z
    constructor
    · intro hz
      have hcoords :
          (z.1 - x.1 = 0 ∧ z.2 - x.2 = 0) ∨
          (z.1 - x.1 = 1 ∧ z.2 - x.2 = 0) ∨
          (z.1 - x.1 = 0 ∧ z.2 - x.2 = 1) ∨
          (z.1 - x.1 = -1 ∧ z.2 - x.2 = 0) ∨
          (z.1 - x.1 = 0 ∧ z.2 - x.2 = -1) := by
        change (z.1 - x.1).natAbs + (z.2 - x.2).natAbs ≤ 1 at hz
        omega
      rcases hcoords with h | h | h | h | h
      · left
        apply Prod.ext
        · have := h.1
          omega
        · have := h.2
          omega
      · right
        left
        apply Prod.ext
        · dsimp [Compass.step]
          have := h.1
          omega
        · dsimp [Compass.step]
          have := h.2
          omega
      · right
        right
        left
        apply Prod.ext
        · dsimp [Compass.step]
          have := h.1
          omega
        · dsimp [Compass.step]
          have := h.2
          omega
      · right
        right
        right
        left
        apply Prod.ext
        · dsimp [Compass.step]
          have := h.1
          omega
        · dsimp [Compass.step]
          have := h.2
          omega
      · right
        right
        right
        right
        apply Prod.ext
        · dsimp [Compass.step]
          have := h.1
          omega
        · dsimp [Compass.step]
          have := h.2
          omega
    · intro hz
      rcases hz with hzx | he | hn | hw | hs
      · rw [hzx]
        simp [latticeDist]
      · rw [he]
        simp [latticeDist, Compass.step]
      · rw [hn]
        simp [latticeDist, Compass.step]
      · rw [hw]
        simp [latticeDist, Compass.step]
      · rw [hs]
        simp [latticeDist, Compass.step]
  have hmember : ∀ z : Plane, z ∈ cross x ↔ latticeDist z x ≤ 1 := by
    intro z
    exact (hcross_list z).trans (hdist_list z).symm
  have hAdj_symm : ∀ a b : Plane, Adjacent a b → Adjacent b a := by
    intro a b hab
    have hfirst : (a.1 - b.1).natAbs = (b.1 - a.1).natAbs := by
      calc
        (a.1 - b.1).natAbs = (-(a.1 - b.1)).natAbs := (Int.natAbs_neg _).symm
        _ = (b.1 - a.1).natAbs := by rw [neg_sub]
    have hsecond : (a.2 - b.2).natAbs = (b.2 - a.2).natAbs := by
      calc
        (a.2 - b.2).natAbs = (-(a.2 - b.2)).natAbs := (Int.natAbs_neg _).symm
        _ = (b.2 - a.2).natAbs := by rw [neg_sub]
    unfold Adjacent latticeDist at *
    rw [hfirst, hsecond] at hab
    exact hab
  have hxmem : x ∈ cross x := by simp [cross]
  have hgeom : ∀ z : Plane, z ∈ cross x → z = x ∨ Adjacent z x := by
    intro z hz
    rcases (hcross_list z).mp hz with hzx | he | hn | hw | hs
    · exact Or.inl hzx
    · right
      rw [he]
      simp [Adjacent, latticeDist, Compass.step]
    · right
      rw [hn]
      simp [Adjacent, latticeDist, Compass.step]
    · right
      rw [hw]
      simp [Adjacent, latticeDist, Compass.step]
    · right
      rw [hs]
      simp [Adjacent, latticeDist, Compass.step]
  have hconnected : ConnectedIn Adjacent (↑(cross x)) := by
    refine ⟨⟨x, hxmem⟩, ?_⟩
    intro u hu v hv
    have hux : JoinedIn Adjacent (↑(cross x)) u x := by
      rcases hgeom u hu with rfl | hux
      · exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl ⟨hu, hxmem, hux⟩
    have hxv : JoinedIn Adjacent (↑(cross x)) x v := by
      rcases hgeom v hv with rfl | hvx
      · exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl ⟨hxmem, hv, hAdj_symm v x hvx⟩
    exact hux.trans hxv
  exact ⟨hcard, hmember, hconnected⟩

#print axioms main

end AKLT.W.WIN025
