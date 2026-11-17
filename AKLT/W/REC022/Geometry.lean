module
public import AKLT.W.REC022.Spin

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC022

theorem adjacent_iff (x z : Plane) : Adjacent x z ↔
    z = (x.1 + 1, x.2) ∨ z = (x.1 - 1, x.2) ∨
    z = (x.1, x.2 + 1) ∨ z = (x.1, x.2 - 1) := by
  rcases x with ⟨a,b⟩
  rcases z with ⟨c,d⟩
  simp only [Adjacent, latticeDist, Prod.mk.injEq]
  omega

theorem adjacent_symm {x z : Plane} (h : Adjacent x z) : Adjacent z x := by
  simp only [Adjacent, latticeDist] at h ⊢
  omega

theorem adjacent_ne {x z : Plane} (h : Adjacent x z) : x ≠ z := by
  rintro rfl
  simp [Adjacent, latticeDist] at h

theorem mem_neighbors_iff (x z : Plane) : z ∈ neighbors x ↔ Adjacent x z := by
  rw [adjacent_iff]
  constructor
  · rintro h
    rcases Finset.mem_image.mp h with ⟨d,_,rfl⟩
    rcases x with ⟨a,b⟩
    cases d <;> simp [Compass.step, sub_eq_add_neg]
  · rintro (rfl | rfl | rfl | rfl)
    · exact Finset.mem_image.mpr ⟨.east, Finset.mem_univ _, by rcases x with ⟨a,b⟩; simp [Compass.step]⟩
    · exact Finset.mem_image.mpr ⟨.west, Finset.mem_univ _, by rcases x with ⟨a,b⟩; simp [Compass.step, sub_eq_add_neg]⟩
    · exact Finset.mem_image.mpr ⟨.north, Finset.mem_univ _, by rcases x with ⟨a,b⟩; simp [Compass.step]⟩
    · exact Finset.mem_image.mpr ⟨.south, Finset.mem_univ _, by rcases x with ⟨a,b⟩; simp [Compass.step, sub_eq_add_neg]⟩

theorem present_symm {G : Finset Plane} {D : Network G} {x z : Plane}
    (h : D.Present x z) : D.Present z x :=
  ⟨h.2.1, h.1, adjacent_symm h.2.2.1, h.2.2.2.2, h.2.2.2.1⟩

theorem mem_presentNeighbors {G : Finset Plane} (D : Network G) (x z : Plane) :
    z ∈ D.presentNeighbors x ↔ D.Present x z := by
  simp only [Network.presentNeighbors, Finset.mem_filter]
  exact ⟨And.right, fun h => ⟨(mem_neighbors_iff x z).mpr h.2.2.1, h⟩⟩

theorem mem_internalBonds {G : Finset Plane} {x z : Plane} :
    (x,z) ∈ internalBonds G ↔ x ∈ G ∧ z ∈ G ∧ z ∈ positiveNeighbors x := by
  simp only [internalBonds, Finset.mem_biUnion, Finset.mem_image, Finset.mem_inter]
  constructor
  · rintro ⟨a, ha, b, ⟨hb, hbG⟩, he⟩
    cases he
    exact ⟨ha, hbG, hb⟩
  · rintro ⟨hx,hz,hpos⟩
    exact ⟨x,hx,z,⟨hpos,hz⟩,rfl⟩

theorem internal_ne {G : Finset Plane} {e : Plane × Plane}
    (h : e ∈ internalBonds G) : e.1 ≠ e.2 := by
  have hp := (mem_internalBonds.mp h).2.2
  simp only [positiveNeighbors, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with h | h <;> intro he
  all_goals rw [← he] at h; have := congrArg Prod.fst h; have := congrArg Prod.snd h; omega

theorem internal_not_reverse {G : Finset Plane} {x z : Plane}
    (h : (x,z) ∈ internalBonds G) : (z,x) ∉ internalBonds G := by
  intro h'
  have h1 := (mem_internalBonds.mp h).2.2
  have h2 := (mem_internalBonds.mp h').2.2
  simp only [positiveNeighbors, Finset.mem_insert, Finset.mem_singleton] at h1 h2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  all_goals have := congrArg Prod.fst h1; have := congrArg Prod.snd h1
            have := congrArg Prod.fst h2; have := congrArg Prod.snd h2; omega

theorem internal_or_reverse {G : Finset Plane} {x z : Plane}
    (hx : x ∈ G) (hz : z ∈ G) (h : Adjacent x z) :
    (x,z) ∈ internalBonds G ∨ (z,x) ∈ internalBonds G := by
  rcases (adjacent_iff x z).mp h with h | h | h | h
  · left; apply mem_internalBonds.mpr; exact ⟨hx,hz,by simp [positiveNeighbors,h]⟩
  · right; apply mem_internalBonds.mpr; refine ⟨hz,hx,?_⟩
    simp [positiveNeighbors,h]
  · left; apply mem_internalBonds.mpr; exact ⟨hx,hz,by simp [positiveNeighbors,h]⟩
  · right; apply mem_internalBonds.mpr; refine ⟨hz,hx,?_⟩
    simp [positiveNeighbors,h]

theorem leg_protected {G : Finset Plane} {e : Plane × Plane}
    (h : e ∈ originalLegs G) : e.1 ∈ protectedSites G := by
  rcases Finset.mem_biUnion.mp h with ⟨x,hx,he⟩
  rcases Finset.mem_image.mp he with ⟨z,hz,rfl⟩
  rcases Finset.mem_sdiff.mp hz with ⟨hn,hout⟩
  have hd : latticeDist x z = 1 := (mem_neighbors_iff x z).mp hn
  apply Finset.mem_filter.mpr
  refine ⟨hx, ?_⟩
  have hl : boundaryDepth G x ≤ (latticeDist x z : ℕ∞) := by
    exact iInf_le (fun w : {z // z ∉ G} => (latticeDist x w.val : ℕ∞)) ⟨z,hout⟩
  rw [hd] at hl
  exact hl.trans (by norm_num)

theorem active_remove {G : Finset Plane} (D : Network G) (y : Plane) :
    (removeSite D y).active = D.active.erase y := by
  ext x
  rw [Network.active, Finset.mem_filter, Finset.mem_erase, Network.active,
    Finset.mem_filter]
  change (x ∈ G ∧ Function.update D.status y .X x ≠ .X) ↔
    x ≠ y ∧ x ∈ G ∧ D.status x ≠ .X
  by_cases h : x = y
  · subst x; simp
  · simp [h]

theorem present_remove {G : Finset Plane} (D : Network G) (y x z : Plane) :
    (removeSite D y).Present x z ↔ D.Present x z ∧ x ≠ y ∧ z ≠ y := by
  simp only [Network.Present, active_remove, Finset.mem_erase]
  tauto

theorem mem_active_remove {G : Finset Plane} (D : Network G) (y x : Plane) :
    x ∈ (removeSite D y).active ↔ x ≠ y ∧ x ∈ D.active := by
  rw [active_remove, Finset.mem_erase]

theorem bonds_remove {G : Finset Plane} (D : Network G) (y : Plane) :
    (removeSite D y).bonds = D.bonds.filter (fun e => e.1 ≠ y ∧ e.2 ≠ y) := by
  ext e
  simp only [Network.bonds, Finset.mem_filter, present_remove]
  tauto

end AKLT.W.REC022
