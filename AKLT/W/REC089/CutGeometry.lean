import AKLT.W.REC089.TemplateGeometry

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC089

attribute [local instance] Classical.propDecidable

abbrev chartEquiv (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass) : Plane ≃ Plane :=
  AKLT.W.REC096.chart a.y incoming

theorem chart_eq (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass) :
    localChart a incoming = chartEquiv a incoming := rfl

theorem chart_mem_local (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass) (z : Plane) :
    localChart a incoming z ∈ localSites a incoming ↔ z ∈ templateSites := by
  change chartEquiv a incoming z ∈ templateSites.image (chartEquiv a incoming) ↔ _
  constructor
  · intro h
    obtain ⟨t, ht, he⟩ := Finset.mem_image.mp h
    exact (chartEquiv a incoming).injective he ▸ ht
  · exact fun h => Finset.mem_image.mpr ⟨z, h, rfl⟩

theorem localSites_sub_G (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass) :
    localSites a incoming ⊆ a.G := by
  intro x hx
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
  exact AKLT.W.REC096.template_interior
    (Finset.mem_filter.mp a.start.1).1 a.start.2.1 incoming hz

def slotEdge (j : Fin 20) : Plane × Plane :=
  ((externalSlot j).1, (externalSlot j).1 + (externalSlot j).2.step)

theorem slotEdge_facts (j : Fin 20) :
    (slotEdge j).1 ∈ templateSites ∧ (slotEdge j).2 ∉ templateSites ∧
      Adjacent (slotEdge j).1 (slotEdge j).2 := by
  revert j
  decide +kernel

theorem slotEdge_injective : Function.Injective slotEdge := by
  decide +kernel

theorem boundary_slot_classification :
    ∀ z : templateSites, ∀ d : Compass, z.val + d.step ∉ templateSites →
      ∃ j, slotEdge j = (z.val, z.val + d.step) := by
  decide +kernel

theorem boundary_slot_exists {z t : Plane} (hz : z ∈ templateSites)
    (ht : t ∉ templateSites) (ha : Adjacent z t) : ∃ j, slotEdge j = (z, t) := by
  obtain ⟨d, _, hd⟩ := Finset.mem_image.mp ((AKLT.W.REC096.adjacent_iff z t).mp ha)
  subst t
  exact boundary_slot_classification ⟨z, hz⟩ d ht

def chartEdge (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass)
    (e : Plane × Plane) : Plane × Plane :=
  AKLT.W.REC003.edge (localChart a incoming e.1) (localChart a incoming e.2)

theorem chartEdge_cases (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass)
    (e : Plane × Plane) :
    chartEdge a incoming e = (localChart a incoming e.1, localChart a incoming e.2) ∨
      chartEdge a incoming e = (localChart a incoming e.2, localChart a incoming e.1) :=
  AKLT.W.REC003.edge_cases _ _

theorem chartEdge_eq_cases (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass)
    {e f : Plane × Plane} (h : chartEdge a incoming e = chartEdge a incoming f) :
    e = f ∨ e = f.swap := by
  have hi := (chartEquiv a incoming).injective
  rcases chartEdge_cases a incoming e with he | he <;>
    rcases chartEdge_cases a incoming f with hf | hf <;> rw [he, hf] at h
  · exact Or.inl (Prod.ext (hi (congrArg Prod.fst h)) (hi (congrArg Prod.snd h)))
  · exact Or.inr (Prod.ext (hi (congrArg Prod.fst h)) (hi (congrArg Prod.snd h)))
  · exact Or.inr (Prod.ext (hi (congrArg Prod.snd h)) (hi (congrArg Prod.fst h)))
  · exact Or.inl (Prod.ext (hi (congrArg Prod.snd h)) (hi (congrArg Prod.fst h)))

theorem chartEdge_injective_internal (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass) :
    Set.InjOn (chartEdge a incoming) (↑(internalBonds templateSites) : Set (Plane × Plane)) := by
  intro e he f hf h
  rcases chartEdge_eq_cases a incoming h with h | h
  · exact h
  · have hp := (AKLT.W.REC003.mem_internal _ _).mp he |>.2.1
    have hq := (AKLT.W.REC003.mem_internal _ _).mp hf |>.2.1
    rw [h] at hp
    exact (AKLT.W.REC003.positive_asymm hq hp).elim

theorem chartEdge_injective_slots (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass) :
    Function.Injective (fun j => chartEdge a incoming (slotEdge j)) := by
  intro i j h
  rcases chartEdge_eq_cases a incoming h with h | h
  · exact slotEdge_injective h
  · have hi := (slotEdge_facts i).1
    rw [h] at hi
    exact ((slotEdge_facts j).2.1 hi).elim

theorem chartEdge_mem (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass)
    {z t : Plane} (h : a.D.Present (localChart a incoming z) (localChart a incoming t)) :
    chartEdge a incoming (z, t) ∈ a.D.bonds :=
  AKLT.W.REC003.edge_mem_bonds h

theorem chartEdge_of_bond (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass)
    {e : Plane × Plane} (he : e ∈ a.D.bonds) :
    chartEdge a incoming ((chartEquiv a incoming).symm e.1,
      (chartEquiv a incoming).symm e.2) = e := by
  have hp := (AKLT.W.REC003.mem_internal _ _).mp (Finset.mem_filter.mp he).1 |>.2.1
  simp only [chartEdge, chart_eq, Equiv.apply_symm_apply]
  simp [AKLT.W.REC003.edge, hp]

def outsideBonds (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass) :=
  a.D.bonds.filter fun e => e.1 ∉ localSites a incoming ∧ e.2 ∉ localSites a incoming

def insideBonds (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass) :=
  (internalBonds templateSites).filter fun e =>
    a.D.Present (localChart a incoming e.1) (localChart a incoming e.2)

def crossingSlots (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass) : Finset (Fin 20) :=
  Finset.univ.filter fun j => a.D.Present
    (localChart a incoming (slotEdge j).1) (localChart a incoming (slotEdge j).2)

theorem bonds_cut_union (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass) :
    a.D.bonds = outsideBonds a incoming ∪
      (insideBonds a incoming).image (chartEdge a incoming) ∪
      (crossingSlots a incoming).image (fun j => chartEdge a incoming (slotEdge j)) := by
  classical
  ext e
  constructor
  · intro he
    have hp := (Finset.mem_filter.mp he).2
    let z := (chartEquiv a incoming).symm e.1
    let t := (chartEquiv a incoming).symm e.2
    have hz : localChart a incoming z = e.1 := (chartEquiv a incoming).apply_symm_apply _
    have ht : localChart a incoming t = e.2 := (chartEquiv a incoming).apply_symm_apply _
    have hpres : a.D.Present (localChart a incoming z) (localChart a incoming t) := by
      rw [hz, ht]; exact hp
    have ha : Adjacent z t :=
      (AKLT.W.REC096.chart_adjacent a.y z t incoming).mp hpres.2.2.1
    by_cases hzi : z ∈ templateSites
    · by_cases hti : t ∈ templateSites
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        have hi := (AKLT.W.REC096.unoriented_internalBonds templateSites z t).mpr ⟨hzi, hti, ha⟩
        rcases hi with hi | hi
        · exact Finset.mem_image.mpr ⟨(z, t), Finset.mem_filter.mpr ⟨hi, hpres⟩,
            chartEdge_of_bond a incoming he⟩
        · refine Finset.mem_image.mpr ⟨(t, z), Finset.mem_filter.mpr
            ⟨hi, AKLT.W.REC003.present_symm hpres⟩, ?_⟩
          rcases chartEdge_cases a incoming (t, z) with h | h
          · have hn := (AKLT.W.REC003.mem_internal _ _).mp (Finset.mem_filter.mp he).1 |>.2.1
            have hrev : e.1 ∈ positiveNeighbours e.2 := by
              have := (AKLT.W.REC003.mem_internal _ _).mp (Finset.mem_filter.mp
                (chartEdge_mem a incoming (AKLT.W.REC003.present_symm hpres))).1 |>.2.1
              simpa [h, hz, ht] using this
            exact (AKLT.W.REC003.positive_asymm hn hrev).elim
          · simpa [hz, ht] using h
      · apply Finset.mem_union_right
        obtain ⟨j, hj⟩ := boundary_slot_exists hzi hti ha
        refine Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · simpa [hj] using hpres
        · rw [hj]; exact chartEdge_of_bond a incoming he
    · by_cases hti : t ∈ templateSites
      · apply Finset.mem_union_right
        obtain ⟨j, hj⟩ := boundary_slot_exists hti hzi (AKLT.W.REC003.adjacent_symm ha)
        refine Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, by simpa [hj] using AKLT.W.REC003.present_symm hpres⟩, ?_⟩
        have hsym : AKLT.W.REC003.edge e.2 e.1 = e := by
          have hn := (AKLT.W.REC003.mem_internal _ _).mp (Finset.mem_filter.mp he).1 |>.2.1
          simp [AKLT.W.REC003.edge, AKLT.W.REC003.positive_asymm hn]
        simpa [hj, chartEdge, hz, ht] using hsym
      · apply Finset.mem_union_left
        apply Finset.mem_union_left
        refine Finset.mem_filter.mpr ⟨he, ?_, ?_⟩
        · rwa [← hz, chart_mem_local]
        · rwa [← ht, chart_mem_local]
  · intro he
    rcases Finset.mem_union.mp he with he | he
    · rcases Finset.mem_union.mp he with he | he
      · exact (Finset.mem_filter.mp he).1
      · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
        exact chartEdge_mem a incoming (Finset.mem_filter.mp hf).2
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp he
      exact chartEdge_mem a incoming (Finset.mem_filter.mp hj).2

#print axioms bonds_cut_union

end AKLT.W.REC089
