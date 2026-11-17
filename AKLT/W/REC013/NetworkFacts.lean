module
public import AKLT.Blueprint.Rec.NodesResponse

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC013

theorem adjacent_symm {x y : Plane} (h : Adjacent x y) : Adjacent y x := by
  unfold Adjacent latticeDist at *
  have h1 : (y.1 - x.1).natAbs = (x.1 - y.1).natAbs := by
    rw [← Int.natAbs_neg (x.1 - y.1), neg_sub]
  have h2 : (y.2 - x.2).natAbs = (x.2 - y.2).natAbs := by
    rw [← Int.natAbs_neg (x.2 - y.2), neg_sub]
  rwa [h1, h2]

theorem present_symm {G : Finset Plane} {D : Network G} {x y : Plane}
    (h : D.Present x y) : D.Present y x :=
  ⟨h.2.1, h.1, adjacent_symm h.2.2.1, h.2.2.2.2, h.2.2.2.1⟩

theorem positive_neighbour_facts {x z : Plane} (h : z ∈ positiveNeighbours x) :
    x ≠ z ∧ z ∈ neighbours x ∧ x ∈ neighbours z := by
  simp only [positiveNeighbours, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl
  · refine ⟨by simp [Prod.ext_iff], ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨Compass.east, Finset.mem_univ _, by simp [Compass.step, Prod.ext_iff]⟩
    · exact Finset.mem_image.mpr ⟨Compass.west, Finset.mem_univ _, by simp [Compass.step, Prod.ext_iff]⟩
  · refine ⟨by simp [Prod.ext_iff], ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨Compass.north, Finset.mem_univ _, by simp [Compass.step, Prod.ext_iff]⟩
    · exact Finset.mem_image.mpr ⟨Compass.south, Finset.mem_univ _, by simp [Compass.step, Prod.ext_iff]⟩

theorem bond_facts {G : Finset Plane} {D : Network G} {e : Plane × Plane}
    (he : e ∈ D.bonds) : e.1 ≠ e.2 ∧ e.2 ∈ D.presentNeighbours e.1 ∧
      e.1 ∈ D.presentNeighbours e.2 := by
  have hp := (Finset.mem_filter.mp he).2
  obtain ⟨x, _, he'⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp he).1
  obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp he'
  have hx : x = e.1 := congrArg Prod.fst heq
  have hzz : z = e.2 := congrArg Prod.snd heq
  have hh := positive_neighbour_facts (Finset.mem_inter.mp hz).1
  subst x z
  exact ⟨hh.1, Finset.mem_filter.mpr ⟨hh.2.1, hp⟩,
    Finset.mem_filter.mpr ⟨hh.2.2, present_symm hp⟩⟩

theorem bond_order {G : Finset Plane} {D : Network G} {e : Plane × Plane}
    (he : e ∈ D.bonds) : e.1.1 + e.1.2 < e.2.1 + e.2.2 := by
  obtain ⟨x, _, he'⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp he).1
  obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp he'
  have hh := (Finset.mem_inter.mp hz).1
  simp only [positiveNeighbours, Finset.mem_insert, Finset.mem_singleton] at hh
  rcases hh with rfl | rfl <;> cases heq <;> dsimp <;> omega

theorem exists_selected_bond {G : Finset Plane} {D : Network G} {y o : Plane}
    (ho : o ∈ D.presentNeighbours y) :
    ∃ e ∈ D.bonds, e = (y,o) ∨ e = (o,y) := by
  have hp := (Finset.mem_filter.mp ho).2
  obtain ⟨d, _, hd⟩ := Finset.mem_image.mp (Finset.mem_filter.mp ho).1
  have hpos {x z : Plane} (h : D.Present x z) (hz : z ∈ positiveNeighbours x) :
      (x,z) ∈ D.bonds := by
    refine Finset.mem_filter.mpr ⟨?_, h⟩
    exact Finset.mem_biUnion.mpr ⟨x, (Finset.mem_filter.mp h.1).1,
      Finset.mem_image.mpr ⟨z,
        Finset.mem_inter.mpr ⟨hz, (Finset.mem_filter.mp h.2.1).1⟩, rfl⟩⟩
  subst o
  cases d
  · exact ⟨(y, y + Compass.east.step), hpos hp (by simp [positiveNeighbours, Compass.step, Prod.ext_iff]), Or.inl rfl⟩
  · exact ⟨(y, y + Compass.north.step), hpos hp (by simp [positiveNeighbours, Compass.step, Prod.ext_iff]), Or.inl rfl⟩
  · exact ⟨(y + Compass.west.step, y), hpos (present_symm hp)
      (by simp [positiveNeighbours, Compass.step, Prod.ext_iff]), Or.inr rfl⟩
  · exact ⟨(y + Compass.south.step, y), hpos (present_symm hp)
      (by simp [positiveNeighbours, Compass.step, Prod.ext_iff]), Or.inr rfl⟩

@[simp] theorem remove_active {G : Finset Plane} (D : Network G) (y x : Plane) :
    x ∈ (removeSite D y).active ↔ x ∈ D.active ∧ x ≠ y := by
  by_cases h : x = y <;> simp [Network.active, removeSite, Function.update_apply, h]

@[simp] theorem trace_active {G : Finset Plane} (D : Network G) (y o x : Plane)
    (hy : D.status y = .D) :
    x ∈ (traceStep D y o).active ↔ x ∈ D.active ∧ x ≠ y := by
  by_cases h : x = y <;> simp [Network.active, traceStep, Function.update_apply, h, hy]

@[simp] theorem remove_bonds {G : Finset Plane} (D : Network G) (y : Plane)
    (e : Plane × Plane) :
    e ∈ (removeSite D y).bonds ↔ e ∈ D.bonds ∧ e.1 ≠ y ∧ e.2 ≠ y := by
  simp only [Network.bonds, Finset.mem_filter]
  simp only [Network.Present, remove_active]
  dsimp only [removeSite]
  tauto

theorem trace_remove_bonds {G : Finset Plane} (D : Network G) (y o : Plane)
    (hy : D.status y = .D) : (traceStep D y o).bonds = (removeSite D y).bonds := by
  have hk {u v : Plane} (hu : u ≠ y) (hv : v ≠ y) :
      v ∈ (traceStep D y o).kept u ↔ v ∈ D.kept u := by
    dsimp only [traceStep]
    split_ifs <;> simp_all
  ext e
  simp only [Network.bonds, Finset.mem_filter]
  simp only [Network.Present, trace_active D y o _ hy, remove_active]
  by_cases h1 : e.1 = y
  · simp [h1]
  by_cases h2 : e.2 = y
  · simp [h2]
  simp only [hk h1 h2, hk h2 h1]
  dsimp only [removeSite]
  rfl

theorem remove_bonds_erase {G : Finset Plane} {D : Network G} {y o : Plane}
    (hs : D.presentNeighbours y = {o}) {e : Plane × Plane} (he : e ∈ D.bonds)
    (hed : e = (y,o) ∨ e = (o,y)) : (removeSite D y).bonds = D.bonds.erase e := by
  have hi (t : Plane × Plane) (ht : t ∈ D.bonds) :
      t.1 = y ∨ t.2 = y → t = e := by
    intro h
    have hh := bond_facts ht
    have hdir : t = (y,o) ∨ t = (o,y) := by
      rcases h with h | h
      · have hto : t.2 = o := by
          have hm := hh.2.1
          rw [h, hs, Finset.mem_singleton] at hm
          exact hm
        exact Or.inl (Prod.ext h hto)
      · have hto : t.1 = o := by
          have hm := hh.2.2
          rw [h, hs, Finset.mem_singleton] at hm
          exact hm
        exact Or.inr (Prod.ext hto h)
    have heo := bond_order he
    have hto := bond_order ht
    rcases hed with heq | heq <;> rcases hdir with htq | htq
    · exact htq.trans heq.symm
    · rw [heq] at heo
      rw [htq] at hto
      dsimp at heo hto
      omega
    · rw [heq] at heo
      rw [htq] at hto
      dsimp at heo hto
      omega
    · exact htq.trans heq.symm
  have he_inc : e.1 = y ∨ e.2 = y := by rcases hed with rfl | rfl <;> simp
  ext t
  rw [remove_bonds, Finset.mem_erase]
  constructor
  · rintro ⟨ht,h1,h2⟩
    exact ⟨fun hh => by subst t; tauto, ht⟩
  · rintro ⟨hne,ht⟩
    exact ⟨ht, fun hh => hne (hi t ht (Or.inl hh)), fun hh => hne (hi t ht (Or.inr hh))⟩

/-- Original leg origins are protected sites of the original volume. -/
theorem leg_origin_protected {G : Finset Plane} (e : originalLegs G) :
    e.val.1 ∈ protectedSites G := by
  obtain ⟨x, hx, h⟩ := Finset.mem_biUnion.mp e.property
  obtain ⟨z, hz, he⟩ := Finset.mem_image.mp h
  have hxx : x = e.val.1 := congrArg Prod.fst he
  have hzz : z = e.val.2 := congrArg Prod.snd he
  subst x z
  obtain ⟨d, _, hd⟩ := Finset.mem_image.mp (Finset.mem_sdiff.mp hz).1
  have hout := (Finset.mem_sdiff.mp hz).2
  have hdist : latticeDist e.val.1 e.val.2 = 1 := by
    rw [← hd]
    cases d <;> norm_num [latticeDist, Compass.step]
  refine Finset.mem_filter.mpr ⟨hx, ?_⟩
  unfold boundaryDepth setDistance
  calc
    _ ≤ (latticeDist e.val.1 e.val.2 : ℕ∞) := iInf_le (fun z : {z // z ∉ G} => (latticeDist e.val.1 z.val : ℕ∞)) ⟨e.val.2, hout⟩
    _ ≤ 2 := by norm_num [hdist]

end AKLT.W.REC013
