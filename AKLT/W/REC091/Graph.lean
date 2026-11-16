import AKLT.W.REC091.Positive

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC091

theorem adjacent_symm {x z : Plane} (h : Adjacent x z) : Adjacent z x := by
  unfold Adjacent latticeDist at h ⊢
  have hx : (z.1 - x.1).natAbs = (x.1 - z.1).natAbs := by
    rw [← Int.natAbs_neg, neg_sub]
  have hz : (z.2 - x.2).natAbs = (x.2 - z.2).natAbs := by
    rw [← Int.natAbs_neg, neg_sub]
  simpa only [hx, hz] using h

theorem present_symm {G : Finset Plane} {D : Network G} {x z : Plane}
    (h : D.Present x z) : D.Present z x :=
  ⟨h.2.1, h.1, adjacent_symm h.2.2.1, h.2.2.2.2, h.2.2.2.1⟩

theorem mem_internalBonds {G : Finset Plane} {e : Plane × Plane} :
    e ∈ internalBonds G ↔ e.1 ∈ G ∧ e.2 ∈ G ∧ e.2 ∈ positiveNeighbours e.1 := by
  constructor
  · intro he
    obtain ⟨x, hx, he⟩ := Finset.mem_biUnion.mp he
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp he
    exact ⟨hx, (Finset.mem_inter.mp hz).2, (Finset.mem_inter.mp hz).1⟩
  · rintro ⟨hx, hz, hp⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨e.1, hx, ?_⟩
    exact Finset.mem_image.mpr ⟨e.2, Finset.mem_inter.mpr ⟨hp, hz⟩, rfl⟩

theorem internalBonds_asymm {G : Finset Plane} {x z : Plane}
    (h : (x, z) ∈ internalBonds G) : (z, x) ∉ internalBonds G := by
  intro hr
  have hp := (mem_internalBonds.mp h).2.2
  have hq := (mem_internalBonds.mp hr).2.2
  simp only [positiveNeighbours, Finset.mem_insert, Finset.mem_singleton] at hp hq
  rcases hp with hp | hp <;> rcases hq with hq | hq
  all_goals
    have hp1 := congrArg Prod.fst hp
    have hp2 := congrArg Prod.snd hp
    have hq1 := congrArg Prod.fst hq
    have hq2 := congrArg Prod.snd hq
    dsimp at *
    omega

theorem positive_neighbour_ne {x z : Plane} (h : z ∈ positiveNeighbours x) : z ≠ x := by
  simp only [positiveNeighbours, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h
  all_goals
    intro he
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    rw [he] at h1 h2
    dsimp at *
    omega

theorem positive_mem_neighbours {x z : Plane} (h : z ∈ positiveNeighbours x) :
    z ∈ neighbours x ∧ x ∈ neighbours z := by
  simp only [positiveNeighbours, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl
  · constructor
    · exact Finset.mem_image.mpr ⟨.east, Finset.mem_univ _, by
        apply Prod.ext <;> simp [Compass.step]⟩
    · apply Finset.mem_image.mpr
      refine ⟨.west, Finset.mem_univ _, ?_⟩
      apply Prod.ext <;> dsimp [Compass.step] <;> omega
  · constructor
    · exact Finset.mem_image.mpr ⟨.north, Finset.mem_univ _, by
        apply Prod.ext <;> simp [Compass.step]⟩
    · apply Finset.mem_image.mpr
      refine ⟨.south, Finset.mem_univ _, ?_⟩
      apply Prod.ext <;> dsimp [Compass.step] <;> omega

theorem present_edge {G : Finset Plane} {D : Network G} {x z : Plane}
    (hz : z ∈ D.presentNeighbours x) : (x, z) ∈ D.bonds ∨ (z, x) ∈ D.bonds := by
  obtain ⟨hn, hp⟩ := Finset.mem_filter.mp hz
  obtain ⟨d, _, hd⟩ := Finset.mem_image.mp hn
  have hxG : x ∈ G := (Finset.mem_filter.mp hp.1).1
  have hzG : z ∈ G := (Finset.mem_filter.mp hp.2.1).1
  have he (hq : z ∈ positiveNeighbours x) : (x, z) ∈ D.bonds :=
    Finset.mem_filter.mpr ⟨mem_internalBonds.mpr ⟨hxG, hzG, hq⟩, hp⟩
  have hr (hq : x ∈ positiveNeighbours z) : (z, x) ∈ D.bonds :=
    Finset.mem_filter.mpr ⟨mem_internalBonds.mpr ⟨hzG, hxG, hq⟩, present_symm hp⟩
  cases d with
  | east =>
    apply Or.inl; apply he
    apply Finset.mem_insert.mpr; left
    rw [← hd]
    apply Prod.ext <;> simp [Compass.step]
  | north =>
    apply Or.inl; apply he
    apply Finset.mem_insert.mpr; right
    apply Finset.mem_singleton.mpr
    rw [← hd]
    apply Prod.ext <;> simp [Compass.step]
  | west =>
    apply Or.inr; apply hr
    apply Finset.mem_insert.mpr; left
    apply Prod.ext
    · have hh := congrArg Prod.fst hd
      dsimp [Compass.step] at hh ⊢
      omega
    · have hh := congrArg Prod.snd hd
      dsimp [Compass.step] at hh ⊢
      omega
  | south =>
    apply Or.inr; apply hr
    apply Finset.mem_insert.mpr; right
    apply Finset.mem_singleton.mpr
    apply Prod.ext
    · have hh := congrArg Prod.fst hd
      dsimp [Compass.step] at hh ⊢
      omega
    · have hh := congrArg Prod.snd hd
      dsimp [Compass.step] at hh ⊢
      omega

def otherEndpoint (y : Plane) (e : Plane × Plane) : Plane :=
  if e.1 = y then e.2 else e.1

theorem incident_image {G : Finset Plane} (D : Network G) (y : Plane) :
    ((D.bonds.filter fun e => e.1 = y ∨ e.2 = y).image (otherEndpoint y)) =
      D.presentNeighbours y := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hb, hy⟩ := Finset.mem_filter.mp he
    obtain ⟨hi, hp⟩ := Finset.mem_filter.mp hb
    have hn := positive_mem_neighbours (mem_internalBonds.mp hi).2.2
    by_cases heq : e.1 = y
    · simp only [otherEndpoint, ite_eq_left heq]
      subst y
      exact Finset.mem_filter.mpr ⟨hn.1, hp⟩
    · have heq' : e.2 = y := hy.resolve_left heq
      simp only [otherEndpoint, ite_eq_right heq]
      subst y
      exact Finset.mem_filter.mpr ⟨hn.2, present_symm hp⟩
  · intro hz
    rcases present_edge hz with hb | hb
    · refine Finset.mem_image.mpr ⟨(y, z), Finset.mem_filter.mpr ⟨hb, Or.inl rfl⟩, ?_⟩
      simp [otherEndpoint]
    · have hne : z ≠ y := positive_neighbour_ne (mem_internalBonds.mp
        (Finset.mem_filter.mp hb).1).2.2 |>.symm
      refine Finset.mem_image.mpr ⟨(z, y), Finset.mem_filter.mpr ⟨hb, Or.inr rfl⟩, ?_⟩
      simp [otherEndpoint, hne]

theorem incident_injective {G : Finset Plane} (D : Network G) (y : Plane) :
    Set.InjOn (otherEndpoint y) (D.bonds.filter fun e => e.1 = y ∨ e.2 = y) := by
  intro e he f hf hsame
  have heB := (Finset.mem_filter.mp he).1
  have hfB := (Finset.mem_filter.mp hf).1
  have heY := (Finset.mem_filter.mp he).2
  have hfY := (Finset.mem_filter.mp hf).2
  by_cases heq : e.1 = y <;> by_cases hfq : f.1 = y
  · apply Prod.ext
    · exact heq.trans hfq.symm
    · simpa [otherEndpoint, heq, hfq] using hsame
  · have hfy : f.2 = y := hfY.resolve_left hfq
    have he2 : e.2 = f.1 := by simpa [otherEndpoint, heq, hfq] using hsame
    have hef : f = (e.2, e.1) := Prod.ext he2.symm (hfy.trans heq.symm)
    exact False.elim (internalBonds_asymm (Finset.mem_filter.mp heB).1
      (hef ▸ (Finset.mem_filter.mp hfB).1))
  · have hey : e.2 = y := heY.resolve_left heq
    have hf2 : f.2 = e.1 := by simpa [otherEndpoint, heq, hfq] using hsame.symm
    have hfe : e = (f.2, f.1) := Prod.ext hf2.symm (hey.trans hfq.symm)
    exact False.elim (internalBonds_asymm (Finset.mem_filter.mp hfB).1
      (hfe ▸ (Finset.mem_filter.mp heB).1))
  · exact Prod.ext (by simpa [otherEndpoint, heq, hfq] using hsame)
      ((heY.resolve_left heq).trans (hfY.resolve_left hfq).symm)

end AKLT.W.REC091
