module
public import AKLT.W.REC002.Sums
public import AKLT.W.REC002.Geometry

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC002

theorem positive_asymm {x z : Plane} (h : z ∈ positiveNeighbours x) :
    x ∉ positiveNeighbours z := by
  simp only [positiveNeighbours, Finset.mem_insert, Finset.mem_singleton,
    Prod.ext_iff] at *
  omega

def otherEnd (y : Plane) (e : Plane × Plane) : Plane := if e.1 = y then e.2 else e.1

theorem incident_other {G : Finset Plane} (D : Network G) (y : Plane)
    (e : Plane × Plane) (he : e ∈ D.bonds.filter (fun e => e.1 = y ∨ e.2 = y)) :
    otherEnd y e ∈ D.presentNeighbours y := by
  obtain ⟨he, h⟩ := Finset.mem_filter.mp he
  have hp := (mem_bonds D e.1 e.2).mp he
  rw [mem_presentNeighbours]
  rcases h with h | h
  · simpa [otherEnd, h] using hp.1
  · have hn : e.1 ≠ y := by simpa [h] using present_ne hp.1
    simpa [otherEnd, hn, h] using (present_symm D e.1 e.2).mp hp.1

theorem incident_injective {G : Finset Plane} (D : Network G) (y : Plane)
    (a b : Plane × Plane)
    (ha : a ∈ D.bonds.filter (fun e => e.1 = y ∨ e.2 = y))
    (hb : b ∈ D.bonds.filter (fun e => e.1 = y ∨ e.2 = y))
    (hab : otherEnd y a = otherEnd y b) : a = b := by
  obtain ⟨ha, hai⟩ := Finset.mem_filter.mp ha
  obtain ⟨hb, hbi⟩ := Finset.mem_filter.mp hb
  have hpa := (mem_bonds D a.1 a.2).mp ha
  have hpb := (mem_bonds D b.1 b.2).mp hb
  by_cases hax : a.1 = y <;> by_cases hbx : b.1 = y
  · apply Prod.ext
    · exact hax.trans hbx.symm
    · simpa [otherEnd, hax, hbx] using hab
  · have hby : b.2 = y := hbi.resolve_left hbx
    have haz : a.2 = b.1 := by simpa [otherEnd, hax, hbx] using hab
    exfalso
    exact positive_asymm hpa.2 (by simpa [hax, haz, hby] using hpb.2)
  · have hay : a.2 = y := hai.resolve_left hax
    have hbz : a.1 = b.2 := by simpa [otherEnd, hax, hbx] using hab
    exfalso
    exact positive_asymm hpb.2 (by simpa [hbx, hbz, hay] using hpa.2)
  · apply Prod.ext
    · simpa [otherEnd, hax, hbx] using hab
    · exact (hai.resolve_left hax).trans (hbi.resolve_left hbx).symm

theorem incident_surjective {G : Finset Plane} (D : Network G) (y z : Plane)
    (hz : z ∈ D.presentNeighbours y) :
    ∃ e ∈ D.bonds.filter (fun e => e.1 = y ∨ e.2 = y), otherEnd y e = z := by
  have hp := (mem_presentNeighbours D y z).mp hz
  rcases (adjacent_iff_positive y z).mp hp.2.2.1 with h | h
  · refine ⟨(y, z), Finset.mem_filter.mpr ⟨(mem_bonds D y z).mpr ⟨hp, h⟩,
      Or.inl rfl⟩, ?_⟩
    simp [otherEnd]
  · refine ⟨(z, y), Finset.mem_filter.mpr ⟨(mem_bonds D z y).mpr
      ⟨(present_symm D y z).mp hp, h⟩, Or.inr rfl⟩, ?_⟩
    simp [otherEnd, (present_ne hp).symm]

theorem bondProduct_remove {G : Finset Plane} (D : Network G) (y : Plane)
    (n : Plane → Vec3) (v : Vec3) :
    bondProduct D.bonds (Function.update n y v) =
      bondProduct (removeSite D y).bonds n *
        ∏ z ∈ D.presentNeighbours y, (1 + dot v (n z)) := by
  unfold bondProduct
  rw [← Finset.prod_filter_not_mul_prod_filter D.bonds
    (fun e => e.1 = y ∨ e.2 = y)]
  congr 1
  · rw [remove_bonds]
    apply Finset.prod_congr (by ext e; simp only [Finset.mem_filter, not_or])
    intro e he
    have h := (Finset.mem_filter.mp he).2
    simp [Function.update_of_ne h.1, Function.update_of_ne h.2]
  · apply Finset.prod_bij (fun e _ => otherEnd y e)
      (fun e he => incident_other D y e he)
      (fun a ha b hb hab => incident_injective D y a b ha hb hab)
      (fun z hz => by
        obtain ⟨e, he, h⟩ := incident_surjective D y z hz
        exact ⟨e, he, h⟩)
    intro e he
    have hp := (mem_bonds D e.1 e.2).mp (Finset.mem_filter.mp he).1
    rcases (Finset.mem_filter.mp he).2 with h | h
    · have hn : e.2 ≠ y := by simpa [h] using (present_ne hp.1).symm
      simp [otherEnd, h, Function.update_of_ne hn]
    · have hn : e.1 ≠ y := by simpa [h] using present_ne hp.1
      simp [otherEnd, hn, h, dot_comm (n e.1) v]

theorem legProduct_remove {G : Finset Plane} (D : Network G) (y : Plane)
    (τ : PinAssignment G) (b : Bool) (hleg : ∀ e : originalLegs G, e.val.1 ≠ y)
    (n : Plane → Vec3) (v : Vec3) :
    legProduct D.active τ b (Function.update n y v) =
      legProduct (removeSite D y).active τ b n := by
  unfold legProduct
  apply Finset.prod_congr rfl
  intro e _
  simp [mem_remove_active, hleg e]

end AKLT.W.REC002
