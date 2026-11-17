import AKLT.Blueprint.Rec.NodesWalk

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC043

private theorem adjacent_orient {x y : Plane} (h : Adjacent x y) :
    y ∈ positiveNeighbours x ∨ x ∈ positiveNeighbours y := by
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  simp only [Adjacent, latticeDist] at h
  simp only [positiveNeighbours, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  omega

private theorem adjacent_symm {x y : Plane} (h : Adjacent x y) : Adjacent y x := by
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  simp only [Adjacent, latticeDist] at *
  omega

private theorem adjacent_ne {x y : Plane} (h : Adjacent x y) : x ≠ y := by
  rintro rfl
  simp [Adjacent, latticeDist] at h

theorem present_symm {G : Finset Plane} {D : Network G} {x y : Plane}
    (h : D.Present x y) : D.Present y x :=
  ⟨h.2.1, h.1, adjacent_symm h.2.2.1, h.2.2.2.2, h.2.2.2.1⟩

theorem traceStep_active_subset {G : Finset Plane} (D : Network G) (u o : Plane) :
    (traceStep D u o).active ⊆ D.active := by
  intro x hx
  simp only [Network.active, Finset.mem_filter] at hx ⊢
  refine ⟨hx.1, ?_⟩
  by_cases h : x = u
  · subst x
    by_cases hs : D.status u = .U
    · simp [hs]
    · simpa [traceStep, hs] using hx.2
  · simpa [traceStep, Function.update_of_ne h] using hx.2

theorem traceStep_kept_subset {G : Finset Plane} (D : Network G) (u o x : Plane) :
    (traceStep D u o).kept x ⊆ D.kept x := by
  dsimp [traceStep]
  split_ifs <;> simp only [Finset.erase_subset, Finset.Subset.refl]

theorem traceStep_present_subset {G : Finset Plane} (D : Network G) (u o : Plane)
    {x y : Plane} (h : (traceStep D u o).Present x y) : D.Present x y :=
  ⟨traceStep_active_subset D u o h.1, traceStep_active_subset D u o h.2.1,
    h.2.2.1, traceStep_kept_subset D u o x h.2.2.2.1,
    traceStep_kept_subset D u o y h.2.2.2.2⟩

theorem traceStep_not_present {G : Finset Plane} (D : Network G) (u o : Plane) :
    ¬ (traceStep D u o).Present u o := by
  intro h
  simpa [traceStep] using h.2.2.2.1

theorem present_mem_bonds {G : Finset Plane} {D : Network G} {x y : Plane}
    (h : D.Present x y) : (x, y) ∈ D.bonds ∨ (y, x) ∈ D.bonds := by
  have hx : x ∈ G := (Finset.mem_filter.mp h.1).1
  have hy : y ∈ G := (Finset.mem_filter.mp h.2.1).1
  rcases adjacent_orient h.2.2.1 with ho | ho
  · left
    apply Finset.mem_filter.mpr
    refine ⟨?_, h⟩
    exact Finset.mem_biUnion.mpr ⟨x, hx,
      Finset.mem_image.mpr ⟨y, Finset.mem_inter.mpr ⟨ho, hy⟩, rfl⟩⟩
  · right
    apply Finset.mem_filter.mpr
    refine ⟨?_, present_symm h⟩
    exact Finset.mem_biUnion.mpr ⟨y, hy,
      Finset.mem_image.mpr ⟨x, Finset.mem_inter.mpr ⟨ho, hx⟩, rfl⟩⟩

/-- Every step consumes an original bond. This does not require a degree premise. -/
theorem traceStep_bonds_card_lt {G : Finset Plane} {D : Network G} {u o : Plane}
    (h : D.Present u o) : (traceStep D u o).bonds.card < D.bonds.card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro e he
    obtain ⟨he, hp⟩ := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr ⟨he, traceStep_present_subset D u o hp⟩
  · intro heq
    rcases present_mem_bonds h with hb | hb
    · have hh : (u, o) ∈ (traceStep D u o).bonds := heq.symm ▸ hb
      exact traceStep_not_present D u o (Finset.mem_filter.mp hh).2
    · have hh : (o, u) ∈ (traceStep D u o).bonds := heq.symm ▸ hb
      exact traceStep_not_present D u o (present_symm (Finset.mem_filter.mp hh).2)

private theorem adjacent_mem_neighbours {x y : Plane} (h : Adjacent x y) :
    y ∈ neighbours x := by
  rcases adjacent_orient h with ho | ho
  · simp only [positiveNeighbours, Finset.mem_insert, Finset.mem_singleton] at ho
    rcases ho with rfl | rfl
    · exact Finset.mem_image.mpr ⟨.east, Finset.mem_univ _, by ext <;> simp [Compass.step]⟩
    · exact Finset.mem_image.mpr ⟨.north, Finset.mem_univ _, by ext <;> simp [Compass.step]⟩
  · simp only [positiveNeighbours, Finset.mem_insert, Finset.mem_singleton] at ho
    rcases ho with ho | ho
    · exact Finset.mem_image.mpr ⟨.west, Finset.mem_univ _, by
        ext <;> simp only [Compass.step, Prod.fst_add, Prod.snd_add, Prod.fst, Prod.snd]
        <;> have hh := congrArg Prod.fst ho <;> have hh' := congrArg Prod.snd ho
        <;> simp only [Prod.fst, Prod.snd] at hh hh' <;> omega⟩
    · exact Finset.mem_image.mpr ⟨.south, Finset.mem_univ _, by
        ext <;> simp only [Compass.step, Prod.fst_add, Prod.snd_add, Prod.fst, Prod.snd]
        <;> have hh := congrArg Prod.fst ho <;> have hh' := congrArg Prod.snd ho
        <;> simp only [Prod.fst, Prod.snd] at hh hh' <;> omega⟩

theorem mem_presentNeighbours {G : Finset Plane} {D : Network G} {x y : Plane}
    (h : D.Present x y) : y ∈ D.presentNeighbours x :=
  Finset.mem_filter.mpr ⟨adjacent_mem_neighbours h.2.2.1, h⟩

theorem traceStep_neighbours_subset {G : Finset Plane} (D : Network G) (u o x : Plane) :
    (traceStep D u o).presentNeighbours x ⊆ D.presentNeighbours x := by
  intro y hy
  obtain ⟨hy, hp⟩ := Finset.mem_filter.mp hy
  exact Finset.mem_filter.mpr ⟨hy, traceStep_present_subset D u o hp⟩

private theorem traceStep_departure_neighbours {G : Finset Plane}
    (D : Network G) (u o : Plane) :
    (traceStep D u o).presentNeighbours u ⊆ (D.presentNeighbours u).erase o := by
  intro y hy
  refine Finset.mem_erase.mpr ⟨?_, traceStep_neighbours_subset D u o u hy⟩
  intro he
  subst y
  exact traceStep_not_present D u o (Finset.mem_filter.mp hy).2

private theorem traceStep_arrival_neighbours {G : Finset Plane}
    (D : Network G) (u o : Plane) :
    (traceStep D u o).presentNeighbours o ⊆ (D.presentNeighbours o).erase u := by
  intro y hy
  refine Finset.mem_erase.mpr ⟨?_, traceStep_neighbours_subset D u o o hy⟩
  intro he
  subst y
  exact traceStep_not_present D u o (present_symm (Finset.mem_filter.mp hy).2)

/-- Auxiliary validity, including all original legs, survives an admissible step. -/
theorem traceStep_auxiliary {G : Finset Plane} {D : Network G}
    (hD : D.Auxiliary) {u o : Plane} (hu : D.AdmissibleStart u) (hp : D.Present u o) :
    (traceStep D u o).Auxiliary := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x hx
    have hxne : x ≠ u := fun he => hx (he ▸ (Finset.mem_filter.mp hu.1).1)
    simpa [traceStep, Function.update_of_ne hxne] using hD.1.1 x hx
  · intro x
    exact (traceStep_kept_subset D u o x).trans (hD.1.2.1 x)
  · intro x hx hs
    by_cases hxu : x = u
    · subst x
      by_cases hU : D.status u = .U
      · have hc := Finset.card_le_card (traceStep_departure_neighbours D u o)
        have hm := mem_presentNeighbours hp
        rw [Finset.card_erase_of_mem hm] at hc
        have hdeg : (D.presentNeighbours u).card ≤ 3 := by
          rcases hu.2.2 with hu | hu
          · exact hu.2
          · simp [hU] at hu
        omega
      · simp [traceStep, hU] at hs
    · have hs' : D.status x = .D := by
        simpa [traceStep, Function.update_of_ne hxu] using hs
      exact (Finset.card_le_card (traceStep_neighbours_subset D u o x)).trans
        (hD.1.2.2.1 x hx hs')
  · intro x hx
    have hd := hD.1.2.2.2 x (traceStep_active_subset D u o hx)
    have hc := Finset.card_le_card (traceStep_neighbours_subset D u o x)
    omega
  · intro x hx
    have hxu : x ≠ u := fun he => hu.2.1 (he ▸ hx)
    simpa [traceStep, Function.update_of_ne hxu] using hD.2 x hx

/-- Before its first hit the fixed target keeps its status and gains no factors. -/
theorem traceStep_target {G : Finset Plane} {D : Network G} {u o v : Plane}
    (hv : AdmissibleTarget D v) (hne : u ≠ v) :
    AdmissibleTarget (traceStep D u o) v := by
  have hstatus : (traceStep D u o).status v = D.status v := by
    simp [traceStep, Function.update_of_ne hne.symm]
  have hactive : v ∈ (traceStep D u o).active := by
    simpa only [Network.active, Finset.mem_filter, hstatus] using hv.1
  refine ⟨hactive, ?_⟩
  have hc := Finset.card_le_card (traceStep_neighbours_subset D u o v)
  rcases hv.2 with ⟨hs, hd⟩ | ⟨hs, hd⟩
  · exact Or.inl ⟨hstatus.trans hs, by omega⟩
  · exact Or.inr ⟨hstatus.trans hs, by omega⟩

/-- Losing the arrival bond gives the next nonprotected endpoint its start bound. -/
theorem traceStep_start {G : Finset Plane} {D : Network G}
    (hD : D.Auxiliary) {u o : Plane} (hp : D.Present u o)
    (ho : o ∉ protectedSites G) : (traceStep D u o).AdmissibleStart o := by
  have hne : o ≠ u := (adjacent_ne hp.2.2.1).symm
  have hstatus : (traceStep D u o).status o = D.status o := by
    simp [traceStep, Function.update_of_ne hne]
  have hactive : o ∈ (traceStep D u o).active := by
    simpa only [Network.active, Finset.mem_filter, hstatus] using hp.2.1
  refine ⟨hactive, ho, ?_⟩
  have hc := Finset.card_le_card (traceStep_arrival_neighbours D u o)
  rw [Finset.card_erase_of_mem (mem_presentNeighbours (present_symm hp))] at hc
  have hG := (Finset.mem_filter.mp hp.2.1).1
  have hnotX := (Finset.mem_filter.mp hp.2.1).2
  cases hs : D.status o with
  | U =>
    have hd := hD.1.2.2.2 o hp.2.1
    exact Or.inl ⟨hstatus.trans hs, by omega⟩
  | D =>
    have hd := hD.1.2.2.1 o hG hs
    exact Or.inr ⟨hstatus.trans hs, by omega⟩
  | X => exact (hnotX hs).elim

private theorem pair_eq_or {x y u o : Plane} (hne : x ≠ y)
    (h : ({x, y} : Finset Plane) = {u, o}) :
    (x = u ∧ y = o) ∨ (x = o ∧ y = u) := by
  have hx : x = u ∨ x = o := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using
      (show x ∈ ({u, o} : Finset Plane) from h ▸ Finset.mem_insert_self x {y})
  have hy : y = u ∨ y = o := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using
      (show y ∈ ({u, o} : Finset Plane) from
        h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self y))
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact (hne rfl).elim
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact (hne rfl).elim

/-- An admissible step deletes precisely the selected unoriented bond.
In particular removing a D departure destroys no unused bond. -/
theorem traceStep_present_iff {G : Finset Plane} {D : Network G} {u o : Plane}
    (hu : D.AdmissibleStart u) (hp : D.Present u o) (x y : Plane) :
    (traceStep D u o).Present x y ↔
      D.Present x y ∧ ({x, y} : Finset Plane) ≠ {u, o} := by
  constructor
  · intro h
    refine ⟨traceStep_present_subset D u o h, ?_⟩
    intro he
    rcases pair_eq_or (adjacent_ne h.2.2.1) he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact traceStep_not_present D x y h
    · exact traceStep_not_present D y x (present_symm h)
  · rintro ⟨h, he⟩
    have hactive (a b : Plane) (hab : D.Present a b)
        (hbond : ({a, b} : Finset Plane) ≠ {u, o}) :
        a ∈ (traceStep D u o).active := by
      have haG := (Finset.mem_filter.mp hab.1).1
      have haX := (Finset.mem_filter.mp hab.1).2
      refine Finset.mem_filter.mpr ⟨haG, ?_⟩
      by_cases hau : a = u
      · subst a
        rcases hu.2.2 with ⟨hU, _⟩ | ⟨hD, hd⟩
        · simp [traceStep, hU]
        · have hbo : b = o := Finset.card_le_one.mp hd b (mem_presentNeighbours hab)
            o (mem_presentNeighbours hp)
          exact (hbond (by rw [hbo])).elim
      · simpa [traceStep, Function.update_of_ne hau] using haX
    refine ⟨hactive x y h he, hactive y x (present_symm h)
      (by simpa only [Finset.pair_comm] using he), h.2.2.1, ?_, ?_⟩
    · by_cases hxu : x = u
      · subst x
        have hyo : y ≠ o := fun hy => he (by rw [hy])
        simpa [traceStep, Finset.mem_erase, hyo] using h.2.2.2.1
      · by_cases hxo : x = o
        · subst x
          have hyu : y ≠ u := fun hy => he (by rw [hy, Finset.pair_comm])
          simpa [traceStep, hxu, Finset.mem_erase, hyu] using h.2.2.2.1
        · simpa [traceStep, hxu, hxo] using h.2.2.2.1
    · by_cases hyu : y = u
      · subst y
        have hxo : x ≠ o := fun hx => he (by rw [hx, Finset.pair_comm])
        simpa [traceStep, Finset.mem_erase, hxo] using h.2.2.2.2
      · by_cases hyo : y = o
        · subst y
          have hxu : x ≠ u := fun hx => he (by rw [hx])
          simpa [traceStep, hyu, Finset.mem_erase, hxu] using h.2.2.2.2
        · simpa [traceStep, hyu, hyo] using h.2.2.2.2

end AKLT.W.REC043
