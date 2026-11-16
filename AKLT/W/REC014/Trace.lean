import AKLT.W.REC014.Geometry

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC014

theorem trace_active {G : Finset Plane} (D : Network G) (y o : Plane)
    (hy : D.status y = .U) : (traceStep D y o).active = D.active := by
  ext x
  simp only [Network.active, Finset.mem_filter]
  by_cases hx : x = y
  · subst x; simp [traceStep, hy]
  · simp [traceStep, hx]

theorem trace_kept_subset {G : Finset Plane} (D : Network G) (y o x : Plane) :
    (traceStep D y o).kept x ⊆ D.kept x := by
  simp only [traceStep]
  split_ifs <;> first | exact Finset.erase_subset _ _ | exact Finset.Subset.refl _

theorem trace_present_old {G : Finset Plane} (D : Network G) (y o : Plane)
    (hy : D.status y = .U) {x z : Plane} (h : (traceStep D y o).Present x z) :
    D.Present x z :=
  ⟨by simpa only [trace_active D y o hy] using h.1,
    by simpa only [trace_active D y o hy] using h.2.1,
    h.2.2.1, trace_kept_subset D y o x h.2.2.2.1,
    trace_kept_subset D y o z h.2.2.2.2⟩

theorem trace_present_away {G : Finset Plane} (D : Network G) (y o : Plane)
    (hy : D.status y = .U) {x z : Plane} (h : D.Present x z)
    (hx : x ≠ y) (hz : z ≠ y) : (traceStep D y o).Present x z := by
  refine ⟨by simpa only [trace_active D y o hy] using h.1,
    by simpa only [trace_active D y o hy] using h.2.1, h.2.2.1, ?_, ?_⟩
  · simp only [traceStep, ite_eq_right hx]
    split_ifs
    · exact Finset.mem_erase.mpr ⟨hz,h.2.2.2.1⟩
    · exact h.2.2.2.1
  · simp only [traceStep, ite_eq_right hz]
    split_ifs
    · exact Finset.mem_erase.mpr ⟨hx,h.2.2.2.2⟩
    · exact h.2.2.2.2

theorem sole_neighbour (a : AKLT.Blueprint.Rec.Departure)
    (hc : (a.D.presentNeighbours a.y).card = 1) {z : Plane}
    (hz : a.D.Present a.y z) : z = a.o :=
  Finset.card_le_one.mp (le_of_eq hc) z (present_neighbour a.D hz) a.o a.present

theorem trace_no_departure (a : AKLT.Blueprint.Rec.Departure)
    (hy : a.D.status a.y = .U) (hc : (a.D.presentNeighbours a.y).card = 1)
    {x z : Plane} (h : (traceStep a.D a.y a.o).Present x z) :
    x ≠ a.y ∧ z ≠ a.y := by
  have hn {t : Plane} (ht : (traceStep a.D a.y a.o).Present a.y t) : False := by
    have ho : t = a.o := sole_neighbour a hc (trace_present_old a.D a.y a.o hy ht)
    have hk := ht.2.2.2.1
    simp [traceStep, ho] at hk
  constructor
  · rintro rfl; exact hn h
  · rintro rfl; exact hn (present_symm _ h)

theorem leaf_bonds (a : AKLT.Blueprint.Rec.Departure)
    (hy : a.D.status a.y = .U) (hc : (a.D.presentNeighbours a.y).card = 1) :
    ∃ e ∈ a.D.bonds,
      ((e.1 = a.y ∧ e.2 = a.o) ∨ (e.1 = a.o ∧ e.2 = a.y)) ∧
      (traceStep a.D a.y a.o).bonds = a.D.bonds.erase e ∧
      ∀ f ∈ a.D.bonds.erase e, f.1 ≠ a.y ∧ f.2 ≠ a.y := by
  obtain ⟨e,he,hform⟩ := present_bond a.D (Finset.mem_filter.mp a.present).2
  have hincident (f) (hf : f ∈ a.D.bonds) (hfy : f.1 = a.y ∨ f.2 = a.y) : f = e := by
    have hp := (Finset.mem_filter.mp hf).2
    have hor : (f.1 = a.y ∧ f.2 = a.o) ∨ (f.1 = a.o ∧ f.2 = a.y) := by
      rcases hfy with h | h
      · exact Or.inl ⟨h, sole_neighbour a hc (h ▸ hp)⟩
      · exact Or.inr ⟨sole_neighbour a hc (h ▸ present_symm a.D hp), h⟩
    apply bond_orientation_unique (Finset.mem_filter.mp hf).1 (Finset.mem_filter.mp he).1
    rcases hor with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;>
      rcases hform with ⟨h3,h4⟩ | ⟨h3,h4⟩ <;> simp_all
  have hrest (f) (hf : f ∈ a.D.bonds.erase e) : f.1 ≠ a.y ∧ f.2 ≠ a.y := by
    obtain ⟨hne,hf⟩ := Finset.mem_erase.mp hf
    exact ⟨fun h => hne (hincident f hf (Or.inl h)),
      fun h => hne (hincident f hf (Or.inr h))⟩
  refine ⟨e,he,hform,?_,hrest⟩
  ext f
  constructor
  · intro hf
    obtain ⟨hfI,hfP⟩ := Finset.mem_filter.mp hf
    have hno := trace_no_departure a hy hc hfP
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_filter.mpr ⟨hfI,trace_present_old _ _ _ hy hfP⟩⟩
    intro hfe
    subst f
    rcases hform with h | h
    · exact hno.1 h.1
    · exact hno.2 h.2
  · intro hf
    have hno := hrest f hf
    obtain ⟨hfI,hfP⟩ := Finset.mem_filter.mp (Finset.mem_of_mem_erase hf)
    exact Finset.mem_filter.mpr ⟨hfI,trace_present_away _ _ _ hy hfP hno.1 hno.2⟩

end AKLT.W.REC014
